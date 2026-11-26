All three statements are gated on the first attempt, with no block: the motive and the relative edge premise are generic in the application exchange, so they instantiate at `Xm` directly.

- **Targets:** `NW…MeasuredRoundTargets.lean`, sha256 `aea17d98…31a1`, recorded in the ledger before the proof was drafted; receipt `build-reports/1795387537346427977-3161633.json`. The hash was re-checked after the proof gate and is unchanged.
- **Proof:** `NW…MeasuredRoundProof.lean`, sha256 `23c94398…0101`; passing receipt `build-reports/1795387581939296076-3161890.json`.
- **Theorems:** `exact_FullyMeasuredApplicationEdgeStepAt`, `exact_FullyMeasuredRoundApplicationLeast`, `exact_FullyMeasuredLeastRepresentativeApplication`. Each depends on `[propext, Classical.choice, Quot.sound]`.
- **Layout:** each definition mirrors its `ExactMeasuredCombined…` counterpart with the application exchange changed from `X` to `Xm`. The one other difference is that the now-unused `let X` is dropped.
- **Edge step:**
  - The measure of `k` comes from `exact_MeasuredExchangePreservesMeasure`, as in the existing step.
  - The least comes from `exact_OpenCoverCombinedRestrictedMeasuredPairedCommonLeast`, fed the accepted edge directly (`acceptEdge (edge4 Xm W) …` is `edgeGraph Xm W …` by definition).
  - Its common least `x` is identified with the held `m` by `valueUnique` and `outputTransport` on `packedLeastProgram`.
- **Round and representative:** the existing proofs with `X` replaced by `Xm`. No private helper had to be copied.
- **Diagnostics:** one linter suggestion to merge two consecutive `intro` lines; nothing else. No existing `.lean` file was edited, nothing deleted, no git.
- **Records:** ledger section "F02 — measured round" appended, plus `fable2/MEASURED-ROUND-EVIDENCE.json` and `fable2/MEASURED-ROUND-SOURCE-MAP.md`.
- **Still an input, not claimed:** the seed application's `Xm` least `m`, and for the representative the function's `Xm` least `x`.
