# A collection of WALs-on-S3 designs

This repo is collecting designs for WALs on object storage in order to understand the various approaches that have been proposed in this area.

Selection criteria:

1. Source of truth only on S3
2. Simple soft-state optimizations allowed
3. Open: either OSS code, a journal article or sufficiently detailed blog post

Exclusion criteria (for now):

1. Storing some durable data on SSDs.
2. Complex metadata service required (SMR-based type of service)

Each design will get a TLA+ specification and eventually added to a classification scheme and final write-up. The final write-up will come once enough designs have been analyzed.

Three main categories:

1. Single-writer WAL (with writer fencing)
2. Multi-writer WAL (for multi-master or decentralized systems)
3. Not quite a WAL but a log all the same.

## Verified designs

So far.

### Category 1: Single-writer WALs

* [SlateDB WAL protocol](slatedb/SlateDBWAL.tla)
    * [Spec desc](slatedb/SlateDBWAL_notes.md)
    * Source https://github.com/slatedb/slatedb
* [SlateDB WAL protocol CAS variant](slatedb/SlateDBWAL_CAS.tla)
    * [Spec desc](slatedb/SlateDBWAL_CAS_notes.md)
* [BufferAsWAL](opendata/BufferAsWAL.tla)
    * [Spec desc](opendata/BufferAsWAL_notes.md)
    * I modified the Buffer design to make it work as a single-writer WAL
* [Objwal](/jay-jamieson-objwal/ObjWAL.tla)
    * [Spec desc](jay-jamieson-objwal/ObjWAL_notes.md)
    * Source: https://github.com/JayJamieson/objwal
* [Shared Storage Consensus](s2c/S2C.tla): 
    * [Spec description](s2c/S2C_notes.md)
    * Source https://github.com/io-s2c/s2c
* [Shared Storage Consensus, fencing variant](s2c/S2CFencing.tla): 
    * [Spec description](s2c/S2CFencing_notes.md)

### Category 2: Multi-writer WALs

* [OSWALD](oswald/)
    * Spec desc, TODO
    * Source: https://nvartolomei.com/oswald, https://github.com/nvartolomei/oswald/tree/main/p
    * Implementations: https://github.com/rockwotj/chorus though its single-writer I believe.
* [Cursor Continuity](cursor/Continuity.tla)
    * [Spec desc](cursor/Continuity_notes.md)
    * Source: https://cursor.com/blog/git-at-any-scale
* [Conflux (Virtual Consensus, LogDrive)](https://github.com/Vanlightly/log-drive-specs/blob/main/tlaplus/AtomicLog.tla)
    * Spec desc, TODO
    * TODO: Make a simplified version for this repo.
    * Source: https://www.usenix.org/system/files/osdi20-balakrishnan.pdf and https://www.usenix.org/system/files/osdi26-vickers.pdf
    *  Some writing: https://jack-vanlightly.com/blog/2026/8/25/the-logdrive-flexible-composition-through-abstraction-in-shared-logs
* [Walgit](/walgit/Walgit.tla)
    * [Spec desc](walgit/walgit_notes.md)
    * Source: https://github.com/tobi/walgit/tree/main

### Category 3: Not quite a WAL but a log or log-like

* OpenData [Buffer](opendata/Buffer.tla)

## Designs yet to model

The following are a set of projects that must be evaluated to see if they qualify and if they do, write the spec for them, and add them to the final analysis. More needed, feel free to suggest!

* Robert Pitt's git3: https://github.com/robertpitt/git3
* OpenData Log
* UnisonDB WAL: https://github.com/ankur-anand/unisondb/tree/main/pkg/walfs
* wal3 chroma https://www.trychroma.com/engineering/wal3
* https://lance.org/format/table/mem_wal/
* https://github.com/rockwotj/chorus
* https://github.com/ankur-anand/objlog
* https://github.com/skipprd/skipprd-wal-p


## Designs not included (due to selection criteria)

* BtrLog (not just S3)
* S2.dev (closed source)
* S2 Lite (defers mostly to SlateDB so not interesting)
* Warpstream, closed source and depends on a non-trivial metadata service