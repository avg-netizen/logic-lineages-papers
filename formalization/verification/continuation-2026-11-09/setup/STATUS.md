# Initial pinned-toolchain setup — 9 November 2026

This setup snapshot starts from reconciled main
`4028a9e34506f4339af2992749464cf2d4d55eb9` on
`formalization/cumulative-continuation-2026-11-09`. Read the
[active continuation release](../../../RESUME-2026-11-09.md).
The numbered register remains **170 checked, 2 inherited, 17 pending / 189**.

Official Lean 4.32.0-rc1 was restored after its archive matched the published
SHA-256 digest. All nine dependency repositories use their existing pinned
commits. The 26 initial upstream imports were restored from 943 matching
official binary-cache archives, with no missing expected objects and one
extraction worker. Restoration invoked no upstream or proof compiler.

At initial setup, the first Outer preflight had 1,187 verified source pins.
Its six modules require a 1,455-module local closure. No local compiled object
was initially present. The 1,377 source-matched inherited successful receipts
remain historical evidence, not substitute binaries or a new successful gate.
Fresh serialized checks are required before accepting new proof work.

Native checks remain coordinator-owned through the unchanged `scripts/check.py`:
2,048 MiB heap, 1,536 MiB RSS, 2,048 MiB minimum free memory, one thread,
90 CPU seconds and 180 wall seconds per compiler. Accepted sources, frozen
targets, dependency/toolchain pins, the checker, manuscripts and CI are unchanged.
No new theorem acceptance, full-root build or remote-CI pass is claimed here.

[TOOLCHAIN.json](TOOLCHAIN.json) records the exact public release and dependency
provenance. Runtime files, caches, local controls and unfinished proof drafts
are not part of this metadata checkpoint.
