/*
 * Copyright (c) 2020-2026 COMBINE-lab.
 *
 * This file is part of libradicl
 * (see https://www.github.com/COMBINE-lab/libradicl).
 *
 * License: 3-clause BSD, see https://opensource.org/licenses/BSD-3-Clause
 */

//! File-descriptor-bounded temporary storage for parallel RAD collation.
//!
//! Each scatter worker owns one append-only spool file.  Records for logical
//! collation buckets are buffered independently, while an in-memory extent
//! index records where each flushed buffer landed in the worker's spool.
//! Gather workers can then replay a logical bucket through [`SegmentedReader`]
//! without creating one temporary file (and one open descriptor) per bucket.

use std::fs::{File, OpenOptions};
use std::io::{self, BufWriter, Read, Seek, SeekFrom, Write};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_SPOOL_ID: AtomicU64 = AtomicU64::new(0);

/// A contiguous byte range in one scatter worker's spool file.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SpoolExtent {
    file_id: u32,
    offset: u64,
    len: u32,
}

/// Per-bucket statistics accumulated without cross-thread atomics.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct SpoolBucketStats {
    pub num_records: u64,
    pub num_bytes: u64,
}

/// A single scatter worker's append-only spool and local bucket buffers.
pub struct BucketSpoolWriter {
    worker_id: u32,
    path: Option<PathBuf>,
    writer: Option<BufWriter<File>>,
    position: u64,
    flush_limit: usize,
    buffers: Vec<Vec<u8>>,
    extents: Vec<Vec<SpoolExtent>>,
    stats: Vec<SpoolBucketStats>,
}

impl BucketSpoolWriter {
    /// Create a worker spool with `num_buckets` logical destinations.
    ///
    /// `flush_limit` is a per-logical-bucket threshold. It is a soft limit:
    /// a single record larger than the threshold is always written intact.
    pub fn new(
        parent: &Path,
        worker_id: u32,
        num_buckets: usize,
        flush_limit: usize,
    ) -> io::Result<Self> {
        let spool_id = NEXT_SPOOL_ID.fetch_add(1, Ordering::Relaxed);
        let path = parent.join(format!(
            ".radicl-collate-spool-{}-{}-{}.tmp",
            std::process::id(),
            spool_id,
            worker_id
        ));
        let file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&path)?;

        Ok(Self {
            worker_id,
            path: Some(path),
            writer: Some(BufWriter::with_capacity(1024 * 1024, file)),
            position: 0,
            flush_limit: flush_limit.max(1),
            buffers: (0..num_buckets).map(|_| Vec::new()).collect(),
            extents: (0..num_buckets).map(|_| Vec::new()).collect(),
            stats: vec![SpoolBucketStats::default(); num_buckets],
        })
    }

    /// Append one complete record to a logical bucket.
    ///
    /// The callback writes directly into the worker-local bucket buffer. The
    /// requested `record_size` is validated against the number of bytes the
    /// callback actually appends.
    pub fn write_record<F>(
        &mut self,
        bucket_id: usize,
        record_size: usize,
        write_record: F,
    ) -> io::Result<()>
    where
        F: FnOnce(&mut Vec<u8>) -> io::Result<()>,
    {
        if bucket_id >= self.buffers.len() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("bucket id {bucket_id} is out of range"),
            ));
        }

        if !self.buffers[bucket_id].is_empty()
            && self.buffers[bucket_id].len().saturating_add(record_size) > self.flush_limit
        {
            self.flush_bucket(bucket_id)?;
        }

        let buffer = &mut self.buffers[bucket_id];
        buffer.reserve(record_size);
        let before = buffer.len();
        write_record(buffer)?;
        let actual = buffer.len() - before;
        if actual != record_size {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("record writer appended {actual} bytes; expected {record_size}"),
            ));
        }

        self.stats[bucket_id].num_records += 1;
        self.stats[bucket_id].num_bytes += actual as u64;

        if buffer.len() >= self.flush_limit {
            self.flush_bucket(bucket_id)?;
        }
        Ok(())
    }

    fn flush_bucket(&mut self, bucket_id: usize) -> io::Result<()> {
        let buffer = &mut self.buffers[bucket_id];
        if buffer.is_empty() {
            return Ok(());
        }

        let len = u32::try_from(buffer.len()).map_err(|_| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                "a single spool extent exceeds the u32 size limit",
            )
        })?;
        self.writer
            .as_mut()
            .expect("spool writer must exist until finish")
            .write_all(buffer)?;
        self.extents[bucket_id].push(SpoolExtent {
            file_id: self.worker_id,
            offset: self.position,
            len,
        });
        self.position += len as u64;
        buffer.clear();
        Ok(())
    }

    /// Flush all logical buckets and return a read-only spool index.
    pub fn finish(mut self) -> io::Result<WorkerSpool> {
        for bucket_id in 0..self.buffers.len() {
            self.flush_bucket(bucket_id)?;
        }
        let mut writer = self
            .writer
            .take()
            .expect("spool writer must exist until finish");
        writer.flush()?;
        drop(writer);

        let path = self
            .path
            .take()
            .expect("spool path must exist until finish");
        let file = File::open(&path)?;
        Ok(WorkerSpool {
            worker_id: self.worker_id,
            path: Some(path),
            file: Some(file),
            extents: std::mem::take(&mut self.extents),
            stats: std::mem::take(&mut self.stats),
        })
    }
}

impl Drop for BucketSpoolWriter {
    fn drop(&mut self) {
        self.writer.take();
        if let Some(path) = self.path.take() {
            let _ = std::fs::remove_file(path);
        }
    }
}

/// Completed output from one scatter worker.
pub struct WorkerSpool {
    worker_id: u32,
    path: Option<PathBuf>,
    file: Option<File>,
    extents: Vec<Vec<SpoolExtent>>,
    stats: Vec<SpoolBucketStats>,
}

impl Drop for WorkerSpool {
    fn drop(&mut self) {
        self.file.take();
        if let Some(path) = self.path.take() {
            let _ = std::fs::remove_file(path);
        }
    }
}

/// Merged read-only view of all scatter-worker spools.
pub struct BucketSpoolSet {
    paths: Vec<PathBuf>,
    files: Option<Arc<Vec<File>>>,
    buckets: Vec<Arc<[SpoolExtent]>>,
    stats: Vec<SpoolBucketStats>,
}

impl BucketSpoolSet {
    /// Merge worker-local indices. Workers may be supplied in any order.
    pub fn from_workers(mut workers: Vec<WorkerSpool>) -> io::Result<Self> {
        if workers.is_empty() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "at least one worker spool is required",
            ));
        }
        workers.sort_unstable_by_key(|worker| worker.worker_id);
        for (expected, worker) in workers.iter().enumerate() {
            if worker.worker_id as usize != expected {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidInput,
                    "worker spool ids must be dense and start at zero",
                ));
            }
        }

        let num_buckets = workers[0].extents.len();
        if workers
            .iter()
            .any(|worker| worker.extents.len() != num_buckets || worker.stats.len() != num_buckets)
        {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "worker spool bucket counts do not match",
            ));
        }

        let mut merged_extents: Vec<Vec<SpoolExtent>> =
            (0..num_buckets).map(|_| Vec::new()).collect();
        let mut stats = vec![SpoolBucketStats::default(); num_buckets];
        for worker in &workers {
            for bucket_id in 0..num_buckets {
                merged_extents[bucket_id].extend_from_slice(&worker.extents[bucket_id]);
                stats[bucket_id].num_records += worker.stats[bucket_id].num_records;
                stats[bucket_id].num_bytes += worker.stats[bucket_id].num_bytes;
            }
        }

        let paths = workers
            .iter_mut()
            .map(|worker| {
                worker
                    .path
                    .take()
                    .expect("completed spool must have a path")
            })
            .collect();
        let files = workers
            .iter_mut()
            .map(|worker| {
                worker
                    .file
                    .take()
                    .expect("completed spool must have a file")
            })
            .collect();
        Ok(Self {
            paths,
            files: Some(Arc::new(files)),
            buckets: merged_extents
                .into_iter()
                .map(|extents| Arc::from(extents.into_boxed_slice()))
                .collect(),
            stats,
        })
    }

    pub fn num_buckets(&self) -> usize {
        self.buckets.len()
    }

    pub fn bucket_stats(&self, bucket_id: usize) -> Option<SpoolBucketStats> {
        self.stats.get(bucket_id).copied()
    }

    /// Create a seekable logical reader over all extents for one bucket.
    pub fn reader(&self, bucket_id: usize) -> io::Result<SegmentedReader> {
        let extents = self.buckets.get(bucket_id).ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("bucket id {bucket_id} is out of range"),
            )
        })?;
        let files = self
            .files
            .as_ref()
            .ok_or_else(|| io::Error::new(io::ErrorKind::NotConnected, "spool files are closed"))?;
        Ok(SegmentedReader::new(files.clone(), extents.clone()))
    }
}

impl Drop for BucketSpoolSet {
    fn drop(&mut self) {
        self.files.take();
        for path in &self.paths {
            let _ = std::fs::remove_file(path);
        }
    }
}

/// A logical `Read + Seek` view over discontiguous worker-spool extents.
pub struct SegmentedReader {
    files: Arc<Vec<File>>,
    extents: Arc<[SpoolExtent]>,
    extent_index: usize,
    extent_offset: u64,
    position: u64,
    len: u64,
}

impl SegmentedReader {
    fn new(files: Arc<Vec<File>>, extents: Arc<[SpoolExtent]>) -> Self {
        let len = extents.iter().map(|extent| extent.len as u64).sum();
        Self {
            files,
            extents,
            extent_index: 0,
            extent_offset: 0,
            position: 0,
            len,
        }
    }

    fn reposition(&mut self, position: u64) {
        self.position = position;
        self.extent_index = 0;
        self.extent_offset = position;
        while self.extent_index < self.extents.len()
            && self.extent_offset >= self.extents[self.extent_index].len as u64
        {
            self.extent_offset -= self.extents[self.extent_index].len as u64;
            self.extent_index += 1;
        }
    }
}

impl Read for SegmentedReader {
    fn read(&mut self, mut output: &mut [u8]) -> io::Result<usize> {
        if output.is_empty() || self.position >= self.len {
            return Ok(0);
        }

        let requested = output.len();
        while !output.is_empty() && self.extent_index < self.extents.len() {
            let extent = self.extents[self.extent_index];
            let remaining = extent.len as u64 - self.extent_offset;
            let take = remaining.min(output.len() as u64) as usize;
            let file = &self.files[extent.file_id as usize];
            let nread = read_at(
                file,
                &mut output[..take],
                extent.offset + self.extent_offset,
            )?;
            if nread == 0 {
                return Err(io::Error::new(
                    io::ErrorKind::UnexpectedEof,
                    "spool extent ended before its indexed length",
                ));
            }

            self.position += nread as u64;
            self.extent_offset += nread as u64;
            let (_, rest) = output.split_at_mut(nread);
            output = rest;

            if self.extent_offset == extent.len as u64 {
                self.extent_index += 1;
                self.extent_offset = 0;
            }
        }
        Ok(requested - output.len())
    }
}

impl Seek for SegmentedReader {
    fn seek(&mut self, position: SeekFrom) -> io::Result<u64> {
        let desired = match position {
            SeekFrom::Start(offset) => i128::from(offset),
            SeekFrom::Current(offset) => i128::from(self.position) + i128::from(offset),
            SeekFrom::End(offset) => i128::from(self.len) + i128::from(offset),
        };
        if !(0..=i128::from(self.len)).contains(&desired) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "invalid seek in segmented spool reader",
            ));
        }
        self.reposition(desired as u64);
        Ok(self.position)
    }
}

#[cfg(unix)]
fn read_at(file: &File, output: &mut [u8], offset: u64) -> io::Result<usize> {
    use std::os::unix::fs::FileExt;
    file.read_at(output, offset)
}

#[cfg(windows)]
fn read_at(file: &File, output: &mut [u8], offset: u64) -> io::Result<usize> {
    use std::os::windows::fs::FileExt;
    file.seek_read(output, offset)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn replays_bucket_extents_across_workers() {
        let parent = std::env::temp_dir();
        let mut worker0 = BucketSpoolWriter::new(&parent, 0, 2, 3).unwrap();
        let mut worker1 = BucketSpoolWriter::new(&parent, 1, 2, 3).unwrap();

        worker0
            .write_record(0, 2, |buffer| {
                buffer.extend_from_slice(b"ab");
                Ok(())
            })
            .unwrap();
        worker0
            .write_record(1, 2, |buffer| {
                buffer.extend_from_slice(b"12");
                Ok(())
            })
            .unwrap();
        worker0
            .write_record(0, 2, |buffer| {
                buffer.extend_from_slice(b"cd");
                Ok(())
            })
            .unwrap();
        worker1
            .write_record(0, 2, |buffer| {
                buffer.extend_from_slice(b"ef");
                Ok(())
            })
            .unwrap();

        let spools = BucketSpoolSet::from_workers(vec![
            worker1.finish().unwrap(),
            worker0.finish().unwrap(),
        ])
        .unwrap();
        assert_eq!(spools.bucket_stats(0).unwrap().num_records, 3);
        assert_eq!(spools.bucket_stats(0).unwrap().num_bytes, 6);

        let mut reader = spools.reader(0).unwrap();
        let mut contents = Vec::new();
        reader.read_to_end(&mut contents).unwrap();
        assert_eq!(contents, b"abcdef");

        reader.seek(SeekFrom::Start(0)).unwrap();
        contents.clear();
        reader.read_to_end(&mut contents).unwrap();
        assert_eq!(contents, b"abcdef");
    }

    #[test]
    fn removes_spool_files_on_drop() {
        let parent = std::env::temp_dir();
        let writer = BucketSpoolWriter::new(&parent, 0, 1, 32).unwrap();
        let unfinished_path = writer.path.clone().unwrap();
        assert!(unfinished_path.exists());
        drop(writer);
        assert!(!unfinished_path.exists());

        let worker = BucketSpoolWriter::new(&parent, 0, 1, 32)
            .unwrap()
            .finish()
            .unwrap();
        let finished_path = worker.path.clone().unwrap();
        let spools = BucketSpoolSet::from_workers(vec![worker]).unwrap();
        assert!(finished_path.exists());
        drop(spools);
        assert!(!finished_path.exists());
    }
}
