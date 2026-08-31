/*
 * Copyright (c) 2020-2026 COMBINE-lab.
 *
 * This file is part of libradicl
 * (see https://www.github.com/COMBINE-lab/libradicl).
 *
 * License: 3-clause BSD, see https://opensource.org/licenses/BSD-3-Clause
 */

//! Parallel collation engine for single-barcode RAD records.

use crate::collation::normalize_collation_resources;
use crate::collation_spool::{BucketSpoolSet, BucketSpoolWriter};
use crate::rad_types::{MappedFragmentOrientation, RadIntId};
use crate::record::{
    AlevinFryReadRecord, AlevinFryReadRecordHeader, AlevinFryReadRecordT, AlevinFryRecordContext,
    CollatableMappedRecord, CollatableRecordHeader, KnownSize, RecordHeader,
    SingleBarcodeRecordScratch,
};
use crate::schema::TempCellInfo;
use ahash::AHashMap;
use anyhow::{Context, bail};
use crossbeam_channel::{Receiver, Sender, bounded};
use scroll::Pread;
use std::io::{BufReader, Cursor, Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

/// Immutable correction and bucket lookup prepared by the workflow layer.
pub struct SingleBarcodeCollationPlan {
    correction_and_bucket: AHashMap<u64, (u64, u32)>,
    num_buckets: usize,
}

impl SingleBarcodeCollationPlan {
    /// Build a collation plan from caller-resolved barcode corrections.
    ///
    /// The caller owns all barcode-resolution semantics.  This constructor
    /// only fuses each accepted `(observed, corrected)` decision with the
    /// logical bucket assigned to the corrected barcode.  Accepting iterators
    /// keeps the public API independent of the caller's map and hasher types.
    pub fn from_corrections<C, G>(
        corrections: C,
        group_to_bucket: G,
        num_buckets: usize,
    ) -> anyhow::Result<Self>
    where
        C: IntoIterator<Item = (u64, u64)>,
        G: IntoIterator<Item = (u64, u32)>,
    {
        if num_buckets == 0 {
            bail!("single-barcode collation requires at least one logical bucket");
        }

        let group_to_bucket: AHashMap<u64, u32> = group_to_bucket.into_iter().collect();
        if group_to_bucket
            .values()
            .any(|&bucket| bucket as usize >= num_buckets)
        {
            bail!("group-to-bucket lookup contains an out-of-range bucket id");
        }

        let corrections = corrections.into_iter();
        let (lower_bound, _) = corrections.size_hint();
        let mut correction_and_bucket = AHashMap::with_capacity(lower_bound);
        for (observed, corrected) in corrections {
            // The historical collator silently ignored correction entries
            // whose target was not in the output permit list. Preserve that
            // behavior instead of imposing a new plan-construction contract.
            if let Some(&bucket) = group_to_bucket.get(&corrected) {
                let resolved = (corrected, bucket);
                if let Some(previous) = correction_and_bucket.insert(observed, resolved)
                    && previous != resolved
                {
                    bail!("observed barcode {observed} has conflicting compiled corrections");
                }
            }
        }
        Ok(Self {
            correction_and_bucket,
            num_buckets,
        })
    }

    /// Compatibility constructor for callers already using `AHashMap`.
    pub fn new(
        correction_map: AHashMap<u64, u64>,
        group_to_bucket: AHashMap<u64, u32>,
        num_buckets: usize,
    ) -> anyhow::Result<Self> {
        Self::from_corrections(correction_map, group_to_bucket, num_buckets)
    }

    pub fn num_buckets(&self) -> usize {
        self.num_buckets
    }
}

#[derive(Clone, Copy, Debug)]
pub struct SingleBarcodeCollationOptions {
    /// Total coordinator and worker threads requested by the caller. Values
    /// below 2 produce a warning and are raised to 2.
    pub num_threads: usize,
    /// Working-memory budget for queues, spool buffers, and gather workers.
    /// Values below 256 MiB produce a warning and are raised to 256 MiB.
    pub memory_budget_bytes: u64,
    pub compress_output: bool,
}

impl Default for SingleBarcodeCollationOptions {
    fn default() -> Self {
        Self {
            num_threads: 8,
            memory_budget_bytes: 2 * 1024 * 1024 * 1024,
            compress_output: false,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct SingleBarcodeCollationStats {
    pub records_scattered: u64,
    pub output_chunks: u64,
    pub num_buckets: usize,
    pub num_scatter_workers: usize,
    pub num_gather_workers: usize,
    pub spool_flush_limit: usize,
    pub scatter_duration: Duration,
    pub gather_duration: Duration,
}

struct ScatterResult {
    spool: crate::collation_spool::WorkerSpool,
    records: u64,
}

enum ScatterRecordHeader {
    U32Pair {
        num_alignments: u32,
        barcode: u32,
        umi: u32,
    },
    U64Pair {
        num_alignments: u32,
        barcode: u64,
        umi: u64,
    },
    Generic(AlevinFryReadRecordHeader<u64>),
}

impl ScatterRecordHeader {
    #[inline]
    fn num_alignments(&self) -> u32 {
        match self {
            Self::U32Pair { num_alignments, .. } => *num_alignments,
            Self::U64Pair { num_alignments, .. } => *num_alignments,
            Self::Generic(header) => header.naln(),
        }
    }

    #[inline]
    fn barcode(&self) -> u64 {
        match self {
            Self::U32Pair { barcode, .. } => u64::from(*barcode),
            Self::U64Pair { barcode, .. } => *barcode,
            Self::Generic(header) => header.collate_key(),
        }
    }

    #[inline]
    fn umi(&self) -> u64 {
        match self {
            Self::U32Pair { umi, .. } => u64::from(*umi),
            Self::U64Pair { umi, .. } => *umi,
            Self::Generic(header) => header.umi,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FixedRecordLayout {
    U32Pair,
    U64Pair,
}

#[inline]
fn fixed_record_layout(context: &AlevinFryRecordContext) -> Option<FixedRecordLayout> {
    match (context.bct, context.umit) {
        (RadIntId::U32, RadIntId::U32) => Some(FixedRecordLayout::U32Pair),
        (RadIntId::U64, RadIntId::U64) => Some(FixedRecordLayout::U64Pair),
        _ => None,
    }
}

#[inline]
fn read_scatter_header(
    reader: &mut Cursor<&[u8]>,
    context: &AlevinFryRecordContext,
    fixed_layout: Option<FixedRecordLayout>,
) -> anyhow::Result<ScatterRecordHeader> {
    let Some(fixed_layout) = fixed_layout else {
        return Ok(ScatterRecordHeader::Generic(
            AlevinFryReadRecord::from_bytes_collatable_header(reader, context)?,
        ));
    };

    let header_bytes = match fixed_layout {
        FixedRecordLayout::U32Pair => 12,
        FixedRecordLayout::U64Pair => 20,
    };
    let start = usize::try_from(reader.position()).context("RAD chunk offset exceeds usize")?;
    let end = start
        .checked_add(header_bytes)
        .context("single-barcode record header offset overflowed")?;
    let bytes = reader
        .get_ref()
        .get(start..end)
        .context("truncated fixed-width single-barcode record header")?;
    reader.set_position(end as u64);
    let num_alignments = u32::from_le_bytes(bytes[0..4].try_into().unwrap());
    Ok(match fixed_layout {
        FixedRecordLayout::U32Pair => ScatterRecordHeader::U32Pair {
            num_alignments,
            barcode: u32::from_le_bytes(bytes[4..8].try_into().unwrap()),
            umi: u32::from_le_bytes(bytes[8..12].try_into().unwrap()),
        },
        FixedRecordLayout::U64Pair => ScatterRecordHeader::U64Pair {
            num_alignments,
            barcode: u64::from_le_bytes(bytes[4..12].try_into().unwrap()),
            umi: u64::from_le_bytes(bytes[12..20].try_into().unwrap()),
        },
    })
}

/// Collate single-barcode records. The reader must be positioned at the first
/// RAD chunk; the caller owns the RAD prelude and file-level tags.
#[allow(clippy::too_many_arguments)]
pub fn collate_single_barcode<R, W>(
    reader: &mut R,
    num_input_chunks: u64,
    record_context: AlevinFryRecordContext,
    plan: Arc<SingleBarcodeCollationPlan>,
    output: Arc<Mutex<W>>,
    temp_parent: &Path,
    expected_orientation: MappedFragmentOrientation,
    mut options: SingleBarcodeCollationOptions,
) -> anyhow::Result<SingleBarcodeCollationStats>
where
    R: Read,
    W: Write + Send + 'static,
{
    (options.num_threads, options.memory_budget_bytes) = normalize_collation_resources(
        "single-barcode collation",
        options.num_threads,
        options.memory_budget_bytes,
    );

    let num_scatter_workers = options.num_threads - 1;
    let tuning_budget = options.memory_budget_bytes.min(2 * 1024 * 1024 * 1024);
    let scatter_buffer_budget = (tuning_budget / 4).clamp(16 * 1024 * 1024, 1024 * 1024 * 1024);
    let spool_flush_limit = usize::try_from(
        scatter_buffer_budget / (num_scatter_workers * plan.num_buckets()).max(1) as u64,
    )
    .unwrap_or(usize::MAX)
    .clamp(1024, 256 * 1024);
    let queue_capacity = (2 * num_scatter_workers).max(2);
    let (work_tx, work_rx) = bounded::<Vec<u8>>(queue_capacity);
    let (recycle_tx, recycle_rx) = bounded::<Vec<u8>>(queue_capacity + 1);

    let scatter_started = Instant::now();
    let mut scatter_handles = Vec::with_capacity(num_scatter_workers);
    for worker_id in 0..num_scatter_workers {
        let work_rx = work_rx.clone();
        let recycle_tx = recycle_tx.clone();
        let plan = plan.clone();
        let context = record_context.clone();
        let parent = temp_parent.to_path_buf();
        scatter_handles.push(thread::spawn(move || {
            scatter_worker(
                worker_id,
                work_rx,
                recycle_tx,
                plan,
                context,
                parent,
                expected_orientation,
                spool_flush_limit,
            )
        }));
    }
    drop(work_rx);
    drop(recycle_tx);

    let mut buffer = Vec::new();
    for _ in 0..num_input_chunks {
        if let Ok(recycled) = recycle_rx.try_recv() {
            buffer = recycled;
        }
        buffer.resize(8, 0);
        reader
            .read_exact(&mut buffer[..8])
            .context("could not read RAD chunk header during scatter")?;
        let chunk_bytes = buffer.pread::<u32>(0)? as usize;
        if chunk_bytes < 8 {
            bail!("invalid RAD chunk length {chunk_bytes}");
        }
        buffer.resize(chunk_bytes, 0);
        reader
            .read_exact(&mut buffer[8..])
            .context("could not read RAD chunk payload during scatter")?;
        work_tx
            .send(buffer)
            .map_err(|_| anyhow::anyhow!("all single-barcode scatter workers stopped"))?;
        buffer = Vec::new();
    }
    drop(work_tx);

    let mut worker_spools = Vec::with_capacity(num_scatter_workers);
    let mut records_scattered = 0_u64;
    for handle in scatter_handles {
        let result = handle
            .join()
            .map_err(|_| anyhow::anyhow!("single-barcode scatter worker panicked"))??;
        records_scattered += result.records;
        worker_spools.push(result.spool);
    }
    let scatter_duration = scatter_started.elapsed();
    let spools = Arc::new(BucketSpoolSet::from_workers(worker_spools)?);

    let gather_started = Instant::now();
    let largest_bucket_bytes = (0..spools.num_buckets())
        .filter_map(|bucket_id| spools.bucket_stats(bucket_id))
        .map(|stats| stats.num_bytes)
        .max()
        .unwrap_or(0);
    let per_gather_worker = largest_bucket_bytes
        .saturating_mul(if options.compress_output { 3 } else { 2 })
        .max(4 * 1024 * 1024);
    let gather_budget = tuning_budget.saturating_mul(3) / 4;
    let budgeted_gather_workers = (gather_budget / per_gather_worker).max(1) as usize;
    let num_gather_workers = (options.num_threads - 1)
        .min(plan.num_buckets())
        .min(budgeted_gather_workers)
        .max(1);
    let (bucket_tx, bucket_rx) = bounded::<usize>((2 * num_gather_workers).max(2));
    let mut gather_handles = Vec::with_capacity(num_gather_workers);
    for _ in 0..num_gather_workers {
        let bucket_rx = bucket_rx.clone();
        let spools = spools.clone();
        let context = record_context.clone();
        let output = output.clone();
        gather_handles.push(thread::spawn(move || -> anyhow::Result<u64> {
            let mut cell_map = crate::schema::U64Map::<TempCellInfo>::default();
            let mut chunks = 0_u64;
            for bucket_id in bucket_rx {
                cell_map.clear();
                let stats = spools
                    .bucket_stats(bucket_id)
                    .context("missing spool bucket statistics")?;
                if stats.num_records == 0 {
                    continue;
                }
                let num_records = u32::try_from(stats.num_records)
                    .context("a collation bucket contains more than u32::MAX records")?;
                let logical_reader = spools.reader(bucket_id)?;
                let mut buffered_reader = BufReader::with_capacity(1024 * 1024, logical_reader);
                chunks += collate_single_barcode_bucket(
                    &mut buffered_reader,
                    &context,
                    num_records,
                    &output,
                    options.compress_output,
                    &mut cell_map,
                )? as u64;
            }
            Ok(chunks)
        }));
    }
    drop(bucket_rx);
    for bucket_id in 0..plan.num_buckets() {
        bucket_tx
            .send(bucket_id)
            .map_err(|_| anyhow::anyhow!("all single-barcode gather workers stopped"))?;
    }
    drop(bucket_tx);

    let mut output_chunks = 0_u64;
    for handle in gather_handles {
        output_chunks += handle
            .join()
            .map_err(|_| anyhow::anyhow!("single-barcode gather worker panicked"))??;
    }
    let gather_duration = gather_started.elapsed();
    drop(spools);

    Ok(SingleBarcodeCollationStats {
        records_scattered,
        output_chunks,
        num_buckets: plan.num_buckets(),
        num_scatter_workers,
        num_gather_workers,
        spool_flush_limit,
        scatter_duration,
        gather_duration,
    })
}

#[allow(clippy::too_many_arguments)]
fn scatter_worker(
    worker_id: usize,
    work_rx: Receiver<Vec<u8>>,
    recycle_tx: Sender<Vec<u8>>,
    plan: Arc<SingleBarcodeCollationPlan>,
    record_context: AlevinFryRecordContext,
    temp_parent: PathBuf,
    expected_orientation: MappedFragmentOrientation,
    spool_flush_limit: usize,
) -> anyhow::Result<ScatterResult> {
    let mut spool = BucketSpoolWriter::new(
        &temp_parent,
        worker_id as u32,
        plan.num_buckets(),
        spool_flush_limit,
    )?;
    let mut scratch = SingleBarcodeRecordScratch::new();
    let mut records = 0_u64;
    let fixed_layout = fixed_record_layout(&record_context);

    for mut bytes in work_rx {
        let mut reader = Cursor::new(bytes.as_slice());
        let mut chunk_header = [0_u8; 8];
        reader.read_exact(&mut chunk_header)?;
        let num_records = chunk_header.pread::<u32>(4)?;
        for _ in 0..num_records {
            let header = read_scatter_header(&mut reader, &record_context, fixed_layout)?;
            let Some(&(corrected_barcode, bucket_id)) =
                plan.correction_and_bucket.get(&header.barcode())
            else {
                skip_alignments(&mut reader, header.num_alignments())?;
                continue;
            };
            scratch.read_filtered(&mut reader, header.num_alignments(), &expected_orientation)?;
            if scratch.is_empty() {
                continue;
            }
            let record_size =
                AlevinFryReadRecord::nbytes(scratch.num_alignments() as u32, &record_context);
            spool.write_record(bucket_id as usize, record_size, |output| {
                scratch
                    .append_corrected(header.umi(), corrected_barcode, &record_context, output)
                    .map_err(std::io::Error::other)
            })?;
            records += 1;
        }
        bytes.clear();
        let _ = recycle_tx.try_send(bytes);
    }

    Ok(ScatterResult {
        spool: spool.finish()?,
        records,
    })
}

fn collate_single_barcode_bucket<T, W>(
    reader: &mut BufReader<T>,
    context: &AlevinFryRecordContext,
    num_records: u32,
    output: &Mutex<W>,
    compress: bool,
    cell_map: &mut crate::schema::U64Map<TempCellInfo>,
) -> anyhow::Result<usize>
where
    T: Read + Seek,
    W: Write,
{
    let Some(fixed_layout) = fixed_record_layout(context) else {
        return Ok(crate::collate_temporary_bucket_twopass_generic::<
            u64,
            _,
            _,
            AlevinFryReadRecordT<u64>,
        >(
            reader, context, num_records, output, compress, cell_map
        ));
    };

    const CHUNK_HEADER_BYTES: usize = 8;
    const ALIGNMENT_BYTES: usize = 4;
    let record_header_bytes = match fixed_layout {
        FixedRecordLayout::U32Pair => 12,
        FixedRecordLayout::U64Pair => 20,
    };
    let mut header = vec![0_u8; record_header_bytes];
    let mut alignment_buffer = vec![0_u8; 64 * 1024];
    let mut total_bytes = 0_usize;

    for _ in 0..num_records {
        reader.read_exact(&mut header)?;
        let num_alignments = header.pread::<u32>(0)? as usize;
        let barcode = match fixed_layout {
            FixedRecordLayout::U32Pair => u64::from(header.pread::<u32>(4)?),
            FixedRecordLayout::U64Pair => header.pread::<u64>(4)?,
        };
        let record_bytes = record_header_bytes + ALIGNMENT_BYTES * num_alignments;
        let cell_info = cell_map.entry(barcode).or_insert(TempCellInfo {
            offset: CHUNK_HEADER_BYTES as u64,
            nbytes: CHUNK_HEADER_BYTES as u32,
            nrec: 0,
        });
        cell_info.offset += record_bytes as u64;
        cell_info.nbytes += record_bytes as u32;
        cell_info.nrec += 1;
        total_bytes += record_bytes;

        let alignment_bytes = ALIGNMENT_BYTES * num_alignments;
        if alignment_buffer.len() < alignment_bytes {
            alignment_buffer.resize(alignment_bytes, 0);
        }
        reader.read_exact(&mut alignment_buffer[..alignment_bytes])?;
    }

    total_bytes += cell_map.len() * CHUNK_HEADER_BYTES;
    let mut output_buffer = Cursor::new(vec![0_u8; total_bytes]);
    let mut next_offset = 0_u64;
    for cell_info in cell_map.values_mut() {
        output_buffer.set_position(next_offset);
        output_buffer.write_all(&cell_info.nbytes.to_le_bytes())?;
        output_buffer.write_all(&cell_info.nrec.to_le_bytes())?;
        cell_info.offset = output_buffer.position();
        next_offset += u64::from(cell_info.nbytes);
    }

    reader.seek(SeekFrom::Start(0))?;
    for _ in 0..num_records {
        reader.read_exact(&mut header)?;
        let num_alignments = header.pread::<u32>(0)? as usize;
        let barcode = match fixed_layout {
            FixedRecordLayout::U32Pair => u64::from(header.pread::<u32>(4)?),
            FixedRecordLayout::U64Pair => header.pread::<u64>(4)?,
        };
        let cell_info = cell_map
            .get_mut(&barcode)
            .context("cell disappeared between collation passes")?;
        output_buffer.set_position(cell_info.offset);
        output_buffer.write_all(&header)?;

        let alignment_bytes = ALIGNMENT_BYTES * num_alignments;
        if alignment_buffer.len() < alignment_bytes {
            alignment_buffer.resize(alignment_bytes, 0);
        }
        reader.read_exact(&mut alignment_buffer[..alignment_bytes])?;
        output_buffer.write_all(&alignment_buffer[..alignment_bytes])?;
        cell_info.offset = output_buffer.position();
    }

    output_buffer.set_position(0);
    if compress {
        let mut compressed =
            snap::write::FrameEncoder::new(Cursor::new(Vec::with_capacity(total_bytes)));
        compressed.write_all(output_buffer.get_ref())?;
        output_buffer = compressed.into_inner()?;
    }
    output
        .lock()
        .map_err(|_| anyhow::anyhow!("collated RAD output mutex was poisoned"))?
        .write_all(output_buffer.get_ref())?;
    Ok(cell_map.len())
}

#[inline]
fn skip_alignments(reader: &mut Cursor<&[u8]>, num_alignments: u32) -> anyhow::Result<()> {
    let bytes = u64::from(num_alignments) * 4;
    let next = reader
        .position()
        .checked_add(bytes)
        .context("alignment skip offset overflowed")?;
    if next > reader.get_ref().len() as u64 {
        bail!("record alignment payload extends beyond its RAD chunk");
    }
    reader.set_position(next);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::record::MappedRecord;
    use scroll::Pwrite;

    #[test]
    fn fixed_header_decoder_falls_back_for_other_integer_widths() {
        let common = AlevinFryRecordContext {
            bct: RadIntId::U64,
            umit: RadIntId::U64,
        };
        assert_eq!(
            fixed_record_layout(&common),
            Some(FixedRecordLayout::U64Pair)
        );
        let current = AlevinFryRecordContext {
            bct: RadIntId::U32,
            umit: RadIntId::U32,
        };
        assert_eq!(
            fixed_record_layout(&current),
            Some(FixedRecordLayout::U32Pair)
        );
        let future = AlevinFryRecordContext {
            bct: RadIntId::U32,
            umit: RadIntId::U16,
        };
        assert_eq!(fixed_record_layout(&future), None);

        let header = AlevinFryReadRecordHeader {
            naln: 2,
            bc: 17_u64,
            umi: 29,
        };
        let mut bytes = Vec::new();
        header.write_fields(&mut bytes, &future).unwrap();
        let mut reader = Cursor::new(bytes.as_slice());
        let decoded =
            read_scatter_header(&mut reader, &future, fixed_record_layout(&future)).unwrap();
        assert!(matches!(decoded, ScatterRecordHeader::Generic(_)));
        assert_eq!(decoded.num_alignments(), 2);
        assert_eq!(decoded.barcode(), 17);
        assert_eq!(decoded.umi(), 29);
        assert_eq!(reader.position(), bytes.len() as u64);
    }

    #[test]
    fn plan_fuses_correction_with_bucket_lookup() {
        let correction = AHashMap::from([(11, 7), (7, 7), (99, 42)]);
        let buckets = AHashMap::from([(7, 2)]);
        let plan = SingleBarcodeCollationPlan::new(correction, buckets, 3).unwrap();
        assert_eq!(plan.correction_and_bucket[&11], (7, 2));
        assert_eq!(plan.correction_and_bucket[&7], (7, 2));
        assert!(!plan.correction_and_bucket.contains_key(&99));
    }

    #[test]
    fn iterator_constructor_is_map_agnostic_and_rejects_conflicts() {
        let plan = SingleBarcodeCollationPlan::from_corrections(
            vec![(11, 7), (7, 7), (99, 42)],
            vec![(7, 2)],
            3,
        )
        .unwrap();
        assert_eq!(plan.correction_and_bucket[&11], (7, 2));
        assert!(!plan.correction_and_bucket.contains_key(&99));

        let error = SingleBarcodeCollationPlan::from_corrections(
            vec![(11, 7), (11, 8)],
            vec![(7, 0), (8, 1)],
            2,
        )
        .err()
        .expect("conflicting compiled decisions must be rejected");
        assert!(
            error
                .to_string()
                .contains("conflicting compiled corrections")
        );
    }

    #[test]
    fn engine_corrects_and_groups_single_barcode_records() {
        let correction = AHashMap::from([(11, 7), (12, 7)]);
        let buckets = AHashMap::from([(7, 0)]);

        // Exercise both fixed-width specializations as well as a mixed-width
        // schema that must use the generic decoder and gather fallback.
        for context in [
            AlevinFryRecordContext {
                bct: RadIntId::U32,
                umit: RadIntId::U32,
            },
            AlevinFryRecordContext {
                bct: RadIntId::U64,
                umit: RadIntId::U64,
            },
            AlevinFryRecordContext {
                bct: RadIntId::U16,
                umit: RadIntId::U32,
            },
        ] {
            let mut chunk = vec![0_u8; 8];
            for (barcode, umi, target) in [(11_u64, 3_u64, 5_u32), (12, 4, 9), (99, 5, 11)] {
                AlevinFryReadRecordHeader {
                    naln: 1,
                    bc: barcode,
                    umi,
                }
                .write_fields(&mut chunk, &context)
                .unwrap();
                chunk.extend_from_slice(&(target | (1_u32 << 31)).to_le_bytes());
            }
            let chunk_bytes = chunk.len() as u32;
            chunk.pwrite::<u32>(chunk_bytes, 0).unwrap();
            chunk.pwrite::<u32>(3, 4).unwrap();

            for compress_output in [false, true] {
                let exercise_resource_clamping = context.bct == RadIntId::U16 && compress_output;
                let plan = Arc::new(
                    SingleBarcodeCollationPlan::new(correction.clone(), buckets.clone(), 1)
                        .unwrap(),
                );
                let output = Arc::new(Mutex::new(Vec::new()));
                let mut input = Cursor::new(chunk.clone());
                let stats = collate_single_barcode(
                    &mut input,
                    1,
                    context.clone(),
                    plan,
                    output.clone(),
                    &std::env::temp_dir(),
                    MappedFragmentOrientation::Unknown,
                    SingleBarcodeCollationOptions {
                        num_threads: if exercise_resource_clamping { 1 } else { 2 },
                        memory_budget_bytes: if exercise_resource_clamping {
                            1024
                        } else {
                            256 * 1024 * 1024
                        },
                        compress_output,
                    },
                )
                .unwrap();
                assert_eq!(stats.records_scattered, 2);
                assert_eq!(stats.output_chunks, 1);
                assert_eq!(stats.num_scatter_workers, 1);

                let encoded = Arc::try_unwrap(output).unwrap().into_inner().unwrap();
                let bytes = if compress_output {
                    let mut decoded = Vec::new();
                    snap::read::FrameDecoder::new(encoded.as_slice())
                        .read_to_end(&mut decoded)
                        .unwrap();
                    decoded
                } else {
                    encoded
                };
                let mut reader = Cursor::new(bytes);
                let mut chunk_header = [0_u8; 8];
                reader.read_exact(&mut chunk_header).unwrap();
                assert_eq!(chunk_header.pread::<u32>(4).unwrap(), 2);
                for expected_umi in [3_u64, 4] {
                    let record =
                        AlevinFryReadRecord::from_bytes_with_context(&mut reader, &context);
                    assert_eq!(record.bc, 7);
                    assert_eq!(record.umi, expected_umi);
                    assert_eq!(record.num_aln(), 1);
                }
            }
        }
    }
}
