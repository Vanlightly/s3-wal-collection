# A collection of WALs-on-S3 designs

This repo is collecting designs for WALs on object storage in order to understand the various approaches that have been proposed in this area.

Likely two main categories:
* Just clients over S3. No servers/clusters for coordination. E.g. OSWALD.
* Some servers required for coordination (for sequencing usually), though that may or may not be soft state. E.g. VirtualConsensus w/ AtomicLog + LogDrive.

Each design will get a TLA+ specification and eventually added to a classification scheme and final write-up. The final write-up will come once enough designs have been analyzed.

## Verified designs

So far:
* [OSWALD](oswald/)
    * Source: https://nvartolomei.com/oswald, https://github.com/nvartolomei/oswald/tree/main/p
    * Implementations: https://github.com/rockwotj/chorus
* Virtual Consensus / AtomicLog + LogDrive.
    * Source: TLA+ here -> https://github.com/Vanlightly/log-drive-specs/blob/main/tlaplus/AtomicLog.tla 


## Designs yet to model

The following are a set of projects that must be evaluated to see if they qualify and if they do, write the spec for them, and add them to the final analysis. More needed, feel free to suggest!

* S2.dev
* BtrLog https://arxiv.org/abs/2606.27051
* Robert Pitt's git3: https://github.com/robertpitt/git3
* Cursor's new WAL thing (Continuity). Enough info for a TLA+ spec?
* OpenData Log + Buffer
* UnisonDB WAL: https://github.com/ankur-anand/unisondb/tree/main/pkg/walfs
* Shared Storage Consensus: https://github.com/io-s2c/s2c