# Accepted uniform kernel separation checkpoint

Paper08 `lem:uniform` is checked on the original numerical source region for every rank `d >= 3`, arbitrary natural masses and requested iteration depth, and arbitrary signed offsets. The printed `C_d = 1000d²` and recursive `T_d` are unchanged. The result includes both separation inequalities, signed depths at least `Phi t`, exact signed-index order, and equality precisely when input, mass, and offset coincide on the existing primitive-recursive common tail.

The focused coordinator `LogicLineages.ExternalCheckpoint20261105UniformSeparation` passed with **169 local modules**, every source hash matched to a successful native row. **Nine main exact aliases and sixteen focused supplier aliases** passed their actual transitive axiom audits, using only `propext`, `Classical.choice`, and `Quot.sound`.

Verification used one worker, a 2048 MiB heap cap, 1536 MiB RSS cap, 2048 MiB free-memory floor, and 90-second CPU / 180-second wall limits per module. The maximum observed successful process-tree RSS was **1,105,000 KiB** (about 1,079 MiB). The pinned Lean/Mathlib artifacts were acquired from their official caches without an upstream rebuild. Three local failed candidates and their raw compiler logs are retained with the repairs; no target, domain, constant, or resource limit was weakened.

Only `08-multivariate-collapse-comparison:lem:uniform` is promoted. The register is **164 checked, 2 inherited, 23 pending / 189**. The earlier finite-source theorem and all pre-existing proof/evidence files are preserved. Full first-order BASE and the polynomial-head comparison chain remain pending. No full-root, previous cumulative-union, or remote-CI build is claimed.

## Evidence

- [Acceptance](ACCEPTANCE.json) and [independent source review](ACCEPTANCE-REVIEW.json).
- [Exact source correspondence](SOURCE-CORRESPONDENCE.md) and [frozen original targets](FROZEN-TARGETS.json).
- [Native verification](NATIVE-VERIFICATION.json), [source pins](SOURCE-PINS.json), and [raw receipts](receipts/).
- [Retained failures and repairs](REPAIRS.json) and [pinned toolchain acquisition](TOOLCHAIN.json).

## Recheck

With the pinned toolchain and upstream cache installed, run from `formalization/`:

```bash
python3 scripts/check.py --memory-mib 2048 --rss-mib 1536 --min-free-mib 2048 LogicLineages.ExternalCheckpoint20261105UniformSeparation
```

The shared checker retains its serialized locks and limits. `tools/collect_evidence.py` can collect fresh native receipts with an explicit `--repo` checkout path; it does not compile or promote a theorem. `tools/acquire_cache.py` preserves the exact session acquisition code and paths as provenance.
