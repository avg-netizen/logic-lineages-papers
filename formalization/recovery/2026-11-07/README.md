# Recovered source snapshot — 7 November 2026

**Status: recovered sources, not natively reverified.**

This checkpoint adds 226 recovered final Lean source files across 29 components at their original repository-relative paths: nine beta-extension sources and 217 later sources. It is an additive snapshot based on `7ddb545ea753c45417ef32ed643cff53745f638c`; existing files, accepted source bytes, configuration and the statement register are preserved.

## Integrity and verification limits

- 98 recovered source files match independently retained original SHA-256 pins.
- 128 recovered source files have no retained original per-source pin. Their current checksums establish snapshot integrity, not independently verified identity to the historically accepted bytes.
- No new native compilation, proof verification, full-root build or remote-CI success is claimed for this recovery. Historical acceptance is not a new verification result.
- The complete original native evidence, dependency closure, compiled artifacts and repository history remain incomplete or unavailable. This checkpoint does not restore the original missing Git commit.
- The statement register remains **168 checked, 2 inherited and 19 pending / 189**. Full paper06 `lem:id1` remains unfinished; no numbered statement is promoted by this recovery.

`SHA256SUMS` contains repository-root-relative SHA-256 checksums for all 226 recovered sources and this README. From the repository root, verify snapshot bytes with:

```sh
sha256sum -c formalization/recovery/2026-11-07/SHA256SUMS
```

This checkpoint includes source and recovery-status material only. It does not resume proof research or compiler work.
