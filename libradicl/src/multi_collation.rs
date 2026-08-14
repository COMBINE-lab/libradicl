/*
 * Copyright (c) 2020-2026 COMBINE-lab.
 *
 * This file is part of libradicl
 * (see https://www.github.com/COMBINE-lab/libradicl).
 *
 * License: 3-clause BSD, see https://opensource.org/licenses/BSD-3-Clause
 */

//! Parallel collation engine for two-level multi-barcode RAD records.

use crate::BarcodeLookupMap;
use crate::collation::BarcodeRole;
use crate::collation::normalize_collation_resources;
use crate::collation_spool::{BucketSpoolSet, BucketSpoolWriter};
use crate::rad_types::MappedFragmentOrientation;
use crate::record::{
    CollatableMappedRecord, CollatableRecordHeader, KnownSize, MultiBarcodeReadRecord,
    MultiBarcodeReadRecordHeader, MultiBarcodeRecordContext, MultiBarcodeRecordScratch,
    RecordHeader,
};
use crate::schema::TempCellInfo;
use ahash::{AHashMap, RandomState};
use anyhow::{Context, bail};
use crossbeam_channel::{Receiver, Sender, bounded};
use scroll::Pread;
use std::collections::{BTreeMap, HashMap};
use std::io::{BufReader, Cursor, Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

/// Correction data for one sparse/global sample position.
pub struct MultiBarcodeSampleCorrection {
    output_ordinal: u64,
    identity: AHashMap<u64, usize>,
    lookup: Option<BarcodeLookupMap>,
    bucket_by_valid_index: Vec<u32>,
}

impl MultiBarcodeSampleCorrection {
    pub fn new(output_ordinal: u64, mut valid_barcodes: Vec<u64>, barcode_len: u32) -> Self {
        valid_barcodes.sort_unstable();
        valid_barcodes.dedup();
        // BarcodeLookupMap's direct-addressed prefix table is deliberately
        // large for fast neighbor queries. Avoid allocating one for every
        // unused position on a mostly empty Flex plate.
        let lookup = (!valid_barcodes.is_empty())
            .then(|| BarcodeLookupMap::new(valid_barcodes, barcode_len));
        let identity = lookup
            .as_ref()
            .map(|lookup| {
                lookup
                    .barcodes
                    .iter()
                    .copied()
                    .enumerate()
                    .map(|(index, barcode)| (barcode, index))
                    .collect()
            })
            .unwrap_or_default();
        Self {
            output_ordinal,
            identity,
            lookup,
            bucket_by_valid_index: Vec::new(),
        }
    }

    pub fn output_ordinal(&self) -> u64 {
        self.output_ordinal
    }

    /// Return the corrected barcode for an identity or unique one-edit match.
    #[inline]
    pub fn correct_barcode(&self, observed: u64) -> Option<u64> {
        if self.identity.contains_key(&observed) {
            return Some(observed);
        }
        let lookup = self.lookup.as_ref()?;
        match lookup.find_neighbors(observed, false) {
            (Some(index), 1) => Some(lookup.barcodes[index]),
            _ => None,
        }
    }

    #[inline]
    fn correction_index(&self, observed: u64) -> Option<usize> {
        if let Some(&index) = self.identity.get(&observed) {
            return Some(index);
        }
        let lookup = self.lookup.as_ref()?;
        match lookup.find_neighbors(observed, false) {
            (Some(index), 1) => Some(index),
            _ => None,
        }
    }

    #[inline]
    fn correct_barcode_and_bucket(&self, observed: u64) -> Option<(u64, u32)> {
        let index = self.correction_index(observed)?;
        let corrected = self.lookup.as_ref()?.barcodes[index];
        let bucket = *self.bucket_by_valid_index.get(index)?;
        Some((corrected, bucket))
    }
}

/// Immutable lookup plan prepared by the workflow layer before collation.
pub struct MultiBarcodeCollationPlan {
    observed_sample_to_index: AHashMap<u64, usize>,
    samples: Vec<MultiBarcodeSampleCorrection>,
    num_buckets: usize,
    gather_groups: Vec<Vec<usize>>,
}

impl MultiBarcodeCollationPlan {
    pub fn new(
        observed_sample_to_index: AHashMap<u64, usize>,
        mut samples: Vec<MultiBarcodeSampleCorrection>,
        group_to_bucket: AHashMap<u64, u32>,
        cell_barcode_bits: u32,
        num_buckets: usize,
    ) -> anyhow::Result<Self> {
        if samples.is_empty() {
            bail!("multi-barcode collation requires at least one sample entry");
        }
        if num_buckets == 0 {
            bail!("multi-barcode collation requires at least one logical bucket");
        }
        if cell_barcode_bits >= 64 {
            bail!("cell barcode keys occupying 64 bits cannot be combined with a sample index");
        }
        if group_to_bucket
            .values()
            .any(|&bucket| bucket as usize >= num_buckets)
        {
            bail!("group-to-bucket lookup contains an out-of-range bucket id");
        }
        if observed_sample_to_index
            .values()
            .any(|&sample_index| sample_index >= samples.len())
        {
            bail!("sample-barcode lookup contains an out-of-range sample index");
        }
        let max_sample_index = u64::MAX >> cell_barcode_bits;
        if samples.len().saturating_sub(1) as u64 > max_sample_index {
            bail!("sample indices and cell barcode bits exceed the composite-key capacity");
        }
        let cell_mask = (1_u64 << cell_barcode_bits) - 1;
        let mut bucket_output_group = vec![None; num_buckets];
        for (sample_index, sample) in samples.iter_mut().enumerate() {
            let Some(lookup) = sample.lookup.as_ref() else {
                continue;
            };
            sample.bucket_by_valid_index.reserve(lookup.barcodes.len());
            for &cell_barcode in &lookup.barcodes {
                let composite =
                    ((sample_index as u64) << cell_barcode_bits) | (cell_barcode & cell_mask);
                let bucket = group_to_bucket.get(&composite).copied().ok_or_else(|| {
                    anyhow::anyhow!(
                        "sample {sample_index} cell barcode {cell_barcode} has no logical bucket"
                    )
                })?;
                let output_group = sample.output_ordinal;
                match bucket_output_group[bucket as usize] {
                    Some(existing) if existing != output_group => {
                        bail!(
                            "logical bucket {bucket} mixes output sample groups {existing} and {output_group}"
                        );
                    }
                    None => bucket_output_group[bucket as usize] = Some(output_group),
                    _ => {}
                }
                sample.bucket_by_valid_index.push(bucket);
            }
        }
        let mut groups_by_ordinal = BTreeMap::<u64, Vec<usize>>::new();
        for (bucket_id, output_group) in bucket_output_group.into_iter().enumerate() {
            if let Some(output_group) = output_group {
                groups_by_ordinal
                    .entry(output_group)
                    .or_default()
                    .push(bucket_id);
            }
        }
        Ok(Self {
            observed_sample_to_index,
            samples,
            num_buckets,
            gather_groups: groups_by_ordinal.into_values().collect(),
        })
    }

    pub fn samples(&self) -> &[MultiBarcodeSampleCorrection] {
        &self.samples
    }

    pub fn num_buckets(&self) -> usize {
        self.num_buckets
    }
}

/// Runtime controls for multi-barcode collation.
#[derive(Clone, Copy, Debug)]
pub struct MultiBarcodeCollationOptions {
    /// Total coordinator and worker threads requested by the caller. Values
    /// below 2 produce a warning and are raised to 2.
    pub num_threads: usize,
    /// Working-memory budget for queues, spool buffers, and gather workers.
    ///
    /// Values below 256 MiB produce a warning and are raised to 256 MiB.
    ///
    /// This does not include the caller-owned correction plan, the operating
    /// system's page cache, allocator overhead, or the output writer.
    pub memory_budget_bytes: u64,
    /// Whether gathered output chunks should be Snappy-framed.
    pub compress_output: bool,
}

impl Default for MultiBarcodeCollationOptions {
    fn default() -> Self {
        Self {
            num_threads: 8,
            memory_budget_bytes: 2 * 1024 * 1024 * 1024,
            compress_output: false,
        }
    }
}

/// Phase and volume statistics returned by [`collate_multi_barcode`].
#[derive(Clone, Debug, Default)]
pub struct MultiBarcodeCollationStats {
    pub records_scattered: u64,
    pub output_chunks: u64,
    pub num_buckets: usize,
    pub num_scatter_workers: usize,
    pub num_gather_workers: usize,
    pub spool_flush_limit: usize,
    pub scatter_duration: Duration,
    pub gather_duration: Duration,
}

#[derive(Clone, Copy, Debug, Default)]
struct WorkerStats {
    scattered: u64,
}

struct ScatterResult {
    spool: crate::collation_spool::WorkerSpool,
    stats: WorkerStats,
}

enum ScatterRecordHeader {
    U32Pair {
        num_alignments: u32,
        sample: u32,
        cell: u32,
        umi: u32,
    },
    Generic(MultiBarcodeReadRecordHeader<u64>),
}

impl ScatterRecordHeader {
    #[inline]
    fn num_alignments(&self) -> u32 {
        match self {
            Self::U32Pair { num_alignments, .. } => *num_alignments,
            Self::Generic(header) => header.naln(),
        }
    }

    #[inline]
    fn observed_sample(&self) -> u64 {
        match self {
            Self::U32Pair { sample, .. } => u64::from(*sample),
            Self::Generic(header) => header.barcodes[0],
        }
    }

    #[inline]
    fn observed_cell(&self) -> u64 {
        match self {
            Self::U32Pair { cell, .. } => u64::from(*cell),
            Self::Generic(header) => header.collate_key(),
        }
    }

    #[inline]
    fn append_corrected(
        &self,
        scratch: &MultiBarcodeRecordScratch,
        context: &MultiBarcodeRecordContext,
        sample_ordinal: u64,
        corrected_cell: u64,
        output: &mut Vec<u8>,
    ) -> anyhow::Result<()> {
        match self {
            Self::U32Pair { umi, .. } => {
                scratch.append_u32_pair_corrected(
                    *umi,
                    sample_ordinal as u32,
                    corrected_cell as u32,
                    output,
                );
                Ok(())
            }
            Self::Generic(header) => {
                scratch.append_corrected(header, context, sample_ordinal, corrected_cell, output)
            }
        }
    }
}

#[inline]
fn is_u32_sample_cell_layout(context: &MultiBarcodeRecordContext) -> bool {
    context.bc_types.as_slice() == [crate::rad_types::RadIntId::U32; 2]
        && context.umit == crate::rad_types::RadIntId::U32
        && context.roles.as_slice() == [BarcodeRole::Sample, BarcodeRole::Cell]
}

#[inline]
fn read_scatter_header(
    reader: &mut Cursor<&[u8]>,
    context: &MultiBarcodeRecordContext,
    u32_sample_cell_layout: bool,
) -> anyhow::Result<ScatterRecordHeader> {
    if !u32_sample_cell_layout {
        return Ok(ScatterRecordHeader::Generic(
            MultiBarcodeReadRecord::from_bytes_collatable_header(reader, context)?,
        ));
    }

    const HEADER_BYTES: usize = 16;
    let start = usize::try_from(reader.position()).context("RAD chunk offset exceeds usize")?;
    let end = start
        .checked_add(HEADER_BYTES)
        .context("multi-barcode record header offset overflowed")?;
    let bytes = reader
        .get_ref()
        .get(start..end)
        .context("truncated two-u32-barcode record header")?;
    reader.set_position(end as u64);

    let read_u32 = |offset: usize| {
        u32::from_le_bytes(
            bytes[offset..offset + 4]
                .try_into()
                .expect("fixed header offsets are in range"),
        )
    };
    Ok(ScatterRecordHeader::U32Pair {
        num_alignments: read_u32(0),
        sample: read_u32(4),
        cell: read_u32(8),
        umi: read_u32(12),
    })
}

/// Collate two-level multi-barcode records from `reader` into `output`.
///
/// The reader must be positioned at the first RAD chunk; the caller remains
/// responsible for reading and writing the RAD prelude and file-level tags.
/// Temporary files are bounded by the number of scatter workers and are
/// removed when the operation finishes or unwinds.
#[allow(clippy::too_many_arguments)]
pub fn collate_multi_barcode<R, W>(
    reader: &mut R,
    num_input_chunks: u64,
    record_context: MultiBarcodeRecordContext,
    plan: Arc<MultiBarcodeCollationPlan>,
    output: Arc<Mutex<W>>,
    temp_parent: &Path,
    expected_orientation: MappedFragmentOrientation,
    mut options: MultiBarcodeCollationOptions,
) -> anyhow::Result<MultiBarcodeCollationStats>
where
    R: Read,
    W: Write + Send + 'static,
{
    (options.num_threads, options.memory_budget_bytes) = normalize_collation_resources(
        "multi-barcode collation",
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
    let mut handles = Vec::with_capacity(num_scatter_workers);
    for worker_id in 0..num_scatter_workers {
        let work_rx = work_rx.clone();
        let recycle_tx = recycle_tx.clone();
        let plan = plan.clone();
        let context = record_context.clone();
        let parent = temp_parent.to_path_buf();
        handles.push(thread::spawn(move || {
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
        let chunk_bytes = buffer
            .pread::<u32>(0)
            .context("could not parse RAD chunk byte count")? as usize;
        if chunk_bytes < 8 {
            bail!("invalid RAD chunk length {chunk_bytes}");
        }
        buffer.resize(chunk_bytes, 0);
        reader
            .read_exact(&mut buffer[8..])
            .context("could not read RAD chunk payload during scatter")?;
        work_tx
            .send(buffer)
            .map_err(|_| anyhow::anyhow!("all multi-barcode scatter workers stopped"))?;
        buffer = Vec::new();
    }
    drop(work_tx);

    let mut worker_spools = Vec::with_capacity(num_scatter_workers);
    let mut records_scattered = 0_u64;
    for handle in handles {
        let result = handle
            .join()
            .map_err(|_| anyhow::anyhow!("multi-barcode scatter worker panicked"))??;
        records_scattered += result.stats.scattered;
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
    // Each gather worker allocates a bucket-sized output buffer and a cell
    // index. Compression needs a second similarly-sized output allocation.
    // Bound concurrency so low-memory configurations trade parallelism for a
    // stable working set instead of merely changing spool buffer sizes.
    let per_gather_worker = largest_bucket_bytes
        .saturating_mul(if options.compress_output { 3 } else { 2 })
        .max(4 * 1024 * 1024);
    let gather_budget = tuning_budget.saturating_mul(3) / 4;
    let budgeted_gather_workers = (gather_budget / per_gather_worker).max(1) as usize;
    let num_gather_workers = (options.num_threads - 1)
        .min(plan.num_buckets())
        .min(budgeted_gather_workers)
        .max(1);
    let (bucket_tx, bucket_rx) = bounded::<usize>(num_gather_workers);
    let (result_tx, result_rx) = bounded::<anyhow::Result<u64>>(num_gather_workers);
    let mut gather_handles = Vec::with_capacity(num_gather_workers);
    for _ in 0..num_gather_workers {
        let bucket_rx = bucket_rx.clone();
        let result_tx = result_tx.clone();
        let spools = spools.clone();
        let context = record_context.clone();
        let output = output.clone();
        gather_handles.push(thread::spawn(move || {
            let state = RandomState::with_seeds(2, 7, 1, 8);
            let mut cell_map = HashMap::<u64, TempCellInfo, RandomState>::with_hasher(state);
            for bucket_id in bucket_rx {
                let result = (|| -> anyhow::Result<u64> {
                    cell_map.clear();
                    let stats = spools
                        .bucket_stats(bucket_id)
                        .context("missing spool bucket statistics")?;
                    if stats.num_records == 0 {
                        return Ok(0);
                    }
                    let num_records = u32::try_from(stats.num_records)
                        .context("a collation bucket contains more than u32::MAX records")?;
                    let logical_reader = spools.reader(bucket_id)?;
                    let mut buffered_reader = BufReader::with_capacity(1024 * 1024, logical_reader);
                    let chunks = collate_multi_barcode_bucket(
                        &mut buffered_reader,
                        &context,
                        num_records,
                        &output,
                        options.compress_output,
                        &mut cell_map,
                    )? as u64;
                    Ok(chunks)
                })();
                if result_tx.send(result).is_err() {
                    break;
                }
            }
        }));
    }
    drop(bucket_rx);
    drop(result_tx);

    let mut output_chunks = 0_u64;
    let mut gather_error = None;
    'gather_groups: for buckets in &plan.gather_groups {
        let initial_window = num_gather_workers.min(buckets.len());
        for &bucket_id in &buckets[..initial_window] {
            if bucket_tx.send(bucket_id).is_err() {
                gather_error = Some(anyhow::anyhow!("all multi-barcode gather workers stopped"));
                break 'gather_groups;
            }
        }
        let mut next_bucket_to_dispatch = initial_window;
        for _ in 0..buckets.len() {
            match result_rx.recv() {
                Ok(Ok(chunks)) => output_chunks += chunks,
                Ok(Err(error)) => {
                    gather_error = Some(error);
                    break 'gather_groups;
                }
                Err(_) => {
                    gather_error =
                        Some(anyhow::anyhow!("all multi-barcode gather workers stopped"));
                    break 'gather_groups;
                }
            }
            if next_bucket_to_dispatch < buckets.len() {
                if bucket_tx.send(buckets[next_bucket_to_dispatch]).is_err() {
                    gather_error =
                        Some(anyhow::anyhow!("all multi-barcode gather workers stopped"));
                    break 'gather_groups;
                }
                next_bucket_to_dispatch += 1;
            }
        }
    }
    drop(bucket_tx);
    drop(result_rx);
    for handle in gather_handles {
        handle
            .join()
            .map_err(|_| anyhow::anyhow!("multi-barcode gather worker panicked"))?;
    }
    if let Some(error) = gather_error {
        return Err(error);
    }
    let gather_duration = gather_started.elapsed();
    drop(spools);

    Ok(MultiBarcodeCollationStats {
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

fn collate_multi_barcode_bucket<T, W>(
    reader: &mut BufReader<T>,
    context: &MultiBarcodeRecordContext,
    num_records: u32,
    output: &Mutex<W>,
    compress: bool,
    cell_map: &mut HashMap<u64, TempCellInfo, RandomState>,
) -> anyhow::Result<usize>
where
    T: Read + Seek,
    W: Write,
{
    if !is_u32_sample_cell_layout(context) {
        return Ok(crate::collate_temporary_bucket_twopass_generic::<
            u64,
            _,
            _,
            MultiBarcodeReadRecord,
        >(
            reader, context, num_records, output, compress, cell_map
        ));
    }

    const CHUNK_HEADER_BYTES: usize = 8;
    const RECORD_HEADER_BYTES: usize = 16;
    const ALIGNMENT_BYTES: usize = 4;
    let mut header = [0_u8; RECORD_HEADER_BYTES];
    let mut alignment_buffer = vec![0_u8; 64 * 1024];
    let mut total_bytes = 0_usize;

    for _ in 0..num_records {
        reader.read_exact(&mut header)?;
        let num_alignments = header.pread::<u32>(0)? as usize;
        let sample = header.pread::<u32>(4)? as u64;
        let cell = header.pread::<u32>(8)? as u64;
        let group_key = (sample << 32) | cell;
        let record_bytes = RECORD_HEADER_BYTES + ALIGNMENT_BYTES * num_alignments;
        let cell_info = cell_map.entry(group_key).or_insert(TempCellInfo {
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
        let sample = header.pread::<u32>(4)? as u64;
        let cell = header.pread::<u32>(8)? as u64;
        let group_key = (sample << 32) | cell;
        let cell_info = cell_map
            .get_mut(&group_key)
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

#[allow(clippy::too_many_arguments)]
fn scatter_worker(
    worker_id: usize,
    work_rx: Receiver<Vec<u8>>,
    recycle_tx: Sender<Vec<u8>>,
    plan: Arc<MultiBarcodeCollationPlan>,
    record_context: MultiBarcodeRecordContext,
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
    let mut scratch = MultiBarcodeRecordScratch::new();
    let mut stats = WorkerStats::default();
    let u32_sample_cell_layout = is_u32_sample_cell_layout(&record_context);

    for mut bytes in work_rx {
        let mut reader = Cursor::new(bytes.as_slice());
        let mut chunk_header = [0_u8; 8];
        reader.read_exact(&mut chunk_header)?;
        let num_records = chunk_header.pread::<u32>(4)?;
        for _ in 0..num_records {
            let header = read_scatter_header(&mut reader, &record_context, u32_sample_cell_layout)?;
            let observed_sample = header.observed_sample();
            let sample_index = plan.observed_sample_to_index.get(&observed_sample).copied();
            let Some(sample_index) = sample_index else {
                skip_alignments(&mut reader, header.num_alignments())?;
                continue;
            };
            let sample = &plan.samples[sample_index];
            let observed_cell = header.observed_cell();
            let Some((corrected_cell, bucket_id)) =
                sample.correct_barcode_and_bucket(observed_cell)
            else {
                skip_alignments(&mut reader, header.num_alignments())?;
                continue;
            };

            scratch.read_filtered(&mut reader, header.num_alignments(), &expected_orientation)?;
            if scratch.is_empty() {
                continue;
            }
            let record_size =
                MultiBarcodeReadRecord::nbytes(scratch.num_alignments() as u32, &record_context);
            spool.write_record(bucket_id as usize, record_size, |output| {
                header
                    .append_corrected(
                        &scratch,
                        &record_context,
                        sample.output_ordinal(),
                        corrected_cell,
                        output,
                    )
                    .map_err(std::io::Error::other)
            })?;
            stats.scattered += 1;
        }
        bytes.clear();
        let _ = recycle_tx.try_send(bytes);
    }

    Ok(ScatterResult {
        spool: spool.finish()?,
        stats,
    })
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
    use crate::collation::BarcodeRole;
    use crate::rad_types::RadIntId;
    use crate::record::{MappedRecord, MultiBarcodeReadRecordHeader};
    use scroll::Pwrite;
    use smallvec::smallvec;
    use std::collections::BTreeMap;

    #[test]
    fn fixed_header_decoder_is_strictly_layout_guarded() {
        let flex_context = MultiBarcodeRecordContext::new(
            smallvec![RadIntId::U32, RadIntId::U32],
            RadIntId::U32,
            smallvec![BarcodeRole::Sample, BarcodeRole::Cell],
        );
        let flex_header: MultiBarcodeReadRecordHeader<u64> = MultiBarcodeReadRecordHeader {
            naln: 3,
            barcodes: smallvec![11, 23],
            umi: 7,
        };
        let mut flex_bytes = Vec::new();
        flex_header
            .write_fields(&mut flex_bytes, &flex_context)
            .unwrap();
        let mut flex_reader = Cursor::new(flex_bytes.as_slice());
        let decoded = read_scatter_header(
            &mut flex_reader,
            &flex_context,
            is_u32_sample_cell_layout(&flex_context),
        )
        .unwrap();
        assert!(matches!(decoded, ScatterRecordHeader::U32Pair { .. }));
        assert_eq!(decoded.num_alignments(), 3);
        assert_eq!(decoded.observed_sample(), 11);
        assert_eq!(decoded.observed_cell(), 23);
        assert_eq!(flex_reader.position(), 16);

        let future_context = MultiBarcodeRecordContext::new(
            smallvec![RadIntId::U16, RadIntId::U32],
            RadIntId::U16,
            smallvec![BarcodeRole::Sample, BarcodeRole::Cell],
        );
        let future_header: MultiBarcodeReadRecordHeader<u64> = MultiBarcodeReadRecordHeader {
            naln: 2,
            barcodes: smallvec![13, 29],
            umi: 5,
        };
        let mut future_bytes = Vec::new();
        future_header
            .write_fields(&mut future_bytes, &future_context)
            .unwrap();
        let mut future_reader = Cursor::new(future_bytes.as_slice());
        let decoded = read_scatter_header(
            &mut future_reader,
            &future_context,
            is_u32_sample_cell_layout(&future_context),
        )
        .unwrap();
        assert!(matches!(decoded, ScatterRecordHeader::Generic(_)));
        assert_eq!(decoded.num_alignments(), 2);
        assert_eq!(decoded.observed_sample(), 13);
        assert_eq!(decoded.observed_cell(), 29);
        assert_eq!(future_reader.position(), future_bytes.len() as u64);

        let different_roles = MultiBarcodeRecordContext::new(
            smallvec![RadIntId::U32, RadIntId::U32],
            RadIntId::U32,
            smallvec![BarcodeRole::Feature, BarcodeRole::Cell],
        );
        assert!(!is_u32_sample_cell_layout(&different_roles));
    }

    #[test]
    fn scatter_worker_rewrites_corrected_barcodes() {
        let context = MultiBarcodeRecordContext::new(
            smallvec![RadIntId::U32, RadIntId::U32],
            RadIntId::U32,
            smallvec![BarcodeRole::Sample, BarcodeRole::Cell],
        );
        let observed_sample = 11_u64;
        let corrected_cell = 23_u64;
        let sample = MultiBarcodeSampleCorrection::new(0, vec![corrected_cell], 16);
        let mut sample_map = AHashMap::new();
        sample_map.insert(observed_sample, 0);
        let composite = corrected_cell;
        let mut group_map = AHashMap::new();
        group_map.insert(composite, 0);
        let plan = Arc::new(
            MultiBarcodeCollationPlan::new(sample_map, vec![sample], group_map, 32, 1).unwrap(),
        );

        let mut chunk = vec![0_u8; 8];
        let header = MultiBarcodeReadRecordHeader {
            naln: 1,
            barcodes: smallvec![observed_sample, corrected_cell],
            umi: 7,
        };
        header.write_fields(&mut chunk, &context).unwrap();
        chunk.extend_from_slice(&(0x8000_0005_u32).to_le_bytes());
        let chunk_len = chunk.len() as u32;
        chunk.pwrite::<u32>(chunk_len, 0).unwrap();
        chunk.pwrite::<u32>(1, 4).unwrap();

        let parent = std::env::temp_dir();
        let (work_tx, work_rx) = bounded(1);
        let (recycle_tx, _recycle_rx) = bounded(1);
        work_tx.send(chunk).unwrap();
        drop(work_tx);
        let result = scatter_worker(
            0,
            work_rx,
            recycle_tx,
            plan,
            context.clone(),
            parent,
            MappedFragmentOrientation::Unknown,
            4096,
        )
        .unwrap();
        assert_eq!(result.stats.scattered, 1);

        let spools = BucketSpoolSet::from_workers(vec![result.spool]).unwrap();
        let mut reader = spools.reader(0).unwrap();
        let record = MultiBarcodeReadRecord::from_bytes_with_context(&mut reader, &context);
        assert_eq!(record.barcodes.as_slice(), &[0, corrected_cell]);
        assert_eq!(record.umi, 7);
        assert_eq!(record.refs, vec![5]);
        assert_eq!(record.dirs, vec![true]);
    }

    #[test]
    fn collation_plan_rejects_buckets_that_mix_sample_groups() {
        let cell = 23_u64;
        let samples = vec![
            MultiBarcodeSampleCorrection::new(0, vec![cell], 16),
            MultiBarcodeSampleCorrection::new(1, vec![cell], 16),
        ];
        let mut group_map = AHashMap::new();
        group_map.insert(cell, 0);
        group_map.insert((1_u64 << 32) | cell, 0);
        let error = MultiBarcodeCollationPlan::new(AHashMap::new(), samples, group_map, 32, 1)
            .err()
            .expect("a gather bucket spanning samples must be rejected");
        assert!(error.to_string().contains("mixes output sample groups"));
    }

    #[test]
    fn specialized_gather_groups_records_with_and_without_compression() {
        let context = MultiBarcodeRecordContext::new(
            smallvec![RadIntId::U32, RadIntId::U32],
            RadIntId::U32,
            smallvec![BarcodeRole::Sample, BarcodeRole::Cell],
        );
        let records = [(1_u32, 7_u32, 2_u32), (0, 5, 3), (1, 7, 4)];
        let mut input = Vec::new();
        for &(sample, cell, umi) in &records {
            input.extend_from_slice(&1_u32.to_le_bytes());
            input.extend_from_slice(&sample.to_le_bytes());
            input.extend_from_slice(&cell.to_le_bytes());
            input.extend_from_slice(&umi.to_le_bytes());
            input.extend_from_slice(&(0x8000_0009_u32).to_le_bytes());
        }

        for compress in [false, true] {
            let mut reader = BufReader::new(Cursor::new(input.as_slice()));
            let output = Mutex::new(Vec::new());
            let state = RandomState::with_seeds(2, 7, 1, 8);
            let mut cell_map = HashMap::with_hasher(state);
            let chunks = collate_multi_barcode_bucket(
                &mut reader,
                &context,
                records.len() as u32,
                &output,
                compress,
                &mut cell_map,
            )
            .unwrap();
            assert_eq!(chunks, 2);

            let encoded = output.into_inner().unwrap();
            let bytes = if compress {
                let mut decoded = Vec::new();
                snap::read::FrameDecoder::new(encoded.as_slice())
                    .read_to_end(&mut decoded)
                    .unwrap();
                decoded
            } else {
                encoded
            };
            let mut collated = Cursor::new(bytes);
            let mut observed = BTreeMap::<(u64, u64), u32>::new();
            while (collated.position() as usize) < collated.get_ref().len() {
                let mut chunk_header = [0_u8; 8];
                collated.read_exact(&mut chunk_header).unwrap();
                let chunk_bytes = chunk_header.pread::<u32>(0).unwrap() as u64;
                let num_records = chunk_header.pread::<u32>(4).unwrap();
                let chunk_start = collated.position() - 8;
                let first =
                    MultiBarcodeReadRecord::from_bytes_with_context(&mut collated, &context);
                observed.insert((first.barcodes[0], first.barcodes[1]), num_records);
                collated.set_position(chunk_start + chunk_bytes);
            }
            assert_eq!(observed, BTreeMap::from([((0, 5), 1), ((1, 7), 2)]));
        }
    }
}
