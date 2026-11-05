# Checked normal-form semantics and numeric compiler

**Eight exact supporting targets are accepted in two gates.** The focused
aggregate `LogicLineages.ExternalCheckpoint20261104NormalForm` passed on the
pinned Lean 4.32.0-rc1 / Mathlib configuration. This checkpoint extends merged
main `ba2dec073b4fc293adf60cfee27efe56142026ff` on
`formalization/cumulative-continuation-2026-11-04`.

The numbered source register remains **161 checked, 2 inherited and 26 pending
out of 189**. Paper08 `thm:snyatkov` remains pending.

## What is now proved

The semantic gate proves exact signed-domain cutoffs, integer row
decomposition, all-occurrence domain guards, nonnegativity/divisibility atom
compilation, arbitrary Boolean compilation, and exact variable membership.
Zero coefficients, cancelled occurrences, repeated names and the hyperfunction's
below-range boundary are all included.

The compiler gate proves exact numeric code calibration and the actual
primitive-recursive item, cutoff, row, domain and atom programs. The concrete
all-code Boolean compiler is also proved primitive recursive, which supplies
the computability required by the unchanged frozen target.

The [source correspondence](SOURCE-CORRESPONDENCE.md) gives the exact scope.
The definitions and target types were restored unchanged from the preceding
successful target-only freeze; their original SHA-256 pins still match.

## Verification

- All **110 local modules** in the focused import closure have successful
  native compiler receipts whose source hashes match the final files.
- The **eight exact aliases** passed transitive axiom audits. The only permitted
  dependencies are `propext`, `Classical.choice` and `Quot.sound`.
- The final aggregate passed after proof-only elaboration repairs. Failed
  attempts, successful receipts, complete compiler logs, source hashes and
  toolchain provenance are preserved in this directory.
- Native compilation used one worker, 2048 MiB heap, 1536 MiB RSS,
  2048 MiB available-memory admission, 90 CPU seconds and 180 wall seconds per
  module. Peak observed RSS was approximately **1151 MiB**.
- The official pinned upstream cache supplied Mathlib objects; no upstream
  build, dependency change or CI configuration change was made.

This is a fresh-checkout verification of the focused local import closure plus
the final incremental aggregate. The complete public root and remote CI were
not run as part of this checkpoint.

With the pinned toolchain and cache available, reproduce the focused check
from `formalization/`:

```sh
python3 scripts/check.py --memory-mib 2048 --rss-mib 1536 --min-free-mib 2048 \
  LogicLineages.ExternalCheckpoint20261104NormalForm
```

The machine-readable entry point is [ACCEPTANCE.json](ACCEPTANCE.json).
[SOURCE-CLOSURE.json](SOURCE-CLOSURE.json) pins the verified local sources;
[COMPILER-LOGS.json](COMPILER-LOGS.json) preserves the complete per-invocation
log bytes as UTF-8 strings with their original SHA-256 values.

## Next source obligations

The eight targets establish the occurrence-row interface, its domains and its
literal compiler. The following whole endpoints remain unproved:

1. `EffectiveSourceExistentialNormalForm`: source-term/Boolean/binding
   normalization with fresh-name and shared-valuation correctness.
2. Full elimination-branch closure, including repeated-occurrence collection,
   remaining domain and dominant-summand cases, and the decreasing
   quantified-block induction.
3. `EffectiveExpandedElimination` and `FullSourceDecision`, including
   inverse-boundary assembly and arbitrary alternating quantifiers.

The previously accepted finite substitution families and comparison consumers
remain available for these steps. No decision oracle or source-normalization
premise has been introduced.
