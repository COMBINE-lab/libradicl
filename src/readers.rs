/*
 * Copyright (c) 2020-2024 COMBINE-lab.
 *
 * This file is part of libradicl
 * (see https://www.github.com/COMBINE-lab/libradicl).
 *
 * License: 3-clause BSD, see https://opensource.org/licenses/BSD-3-Clause
 */

use libradicl::header::{RadPrelude, RadHeader};
use libradicl::record::RadReadRecord;
use std::sync::Arc;
use crossbeam_queue::ArrayQueue;

struct MetaChunk {
}

#[derive(Debug)]
struct ParallelRadReader<R: MappedRecord, 'a> {
    prelude: &'a RadPrelude,
    meta_chunk_queue: Arc<ArrayQueue<MetaChunk>>,
}
