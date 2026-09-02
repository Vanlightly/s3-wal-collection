# A collection of WALs-on-S3 designs

This repo is collecting designs for WALs on object storage in order to understand the various approaches that have been proposed in this area.

Selection criteria:

1. Source of truth only on S3
2. Simple soft-state optimizations allowed

Exclusion criteria (for now):

1. Storing some durable data on SSDs.
2. Complex metadata service required (SMR-based type of service)

Each design will get a TLA+ specification and eventually added to a classification scheme and final write-up. The final write-up will come once enough designs have been analyzed.

Three main categories:

1. Single-writer WAL (with writer fencing)
2. Multi-writer WAL (for multi-master systems)
3. Not quite a WAL but a log all the same.

## Verified designs

So far.

Single-writer WALs:

* [OSWALD](oswald/)
    * Source: https://nvartolomei.com/oswald, https://github.com/nvartolomei/oswald/tree/main/p
    * Implementations: https://github.com/rockwotj/chorus though its single-writer I believe.
* [BufferAsWAL](opendata/BufferAsWAL.tla)
    * I modified the Buffer design to make it work as a single-writer WAL

Multi-writer WALs:

* Conflux (Virtual Consensus, LogDrive)
    * Absractions over cloud storage, including S3. S3 the whole source of truth.
    * Soft-state optimizations
    * TODO: Make a simplified version for this repo.
    * Source: https://www.usenix.org/system/files/osdi20-balakrishnan.pdf and https://www.usenix.org/system/files/osdi26-vickers.pdf
    * TLA+ here -> https://github.com/Vanlightly/log-drive-specs/blob/main/tlaplus/AtomicLog.tla 
    *  Some writing: https://jack-vanlightly.com/blog/2026/8/25/the-logdrive-flexible-composition-through-abstraction-in-shared-logs

Not quite a WAL:

* OpenData [Buffer](opendata/Buffer.tla)


## Designs yet to model

The following are a set of projects that must be evaluated to see if they qualify and if they do, write the spec for them, and add them to the final analysis. More needed, feel free to suggest!

* SlateDB WAL https://github.com/slatedb/slatedb/blob/main/specs/fizzbee/WalProtocol.fizz, https://www.bitsxpages.com/p/protocols-for-transactional-usage
* S2.dev
* Robert Pitt's git3: https://github.com/robertpitt/git3
* Cursor's new WAL thing (Continuity). Enough info for a TLA+ spec?
* OpenData Log
* UnisonDB WAL: https://github.com/ankur-anand/unisondb/tree/main/pkg/walfs
* Shared Storage Consensus: https://github.com/io-s2c/s2c
* objwal https://github.com/JayJamieson/objwal
