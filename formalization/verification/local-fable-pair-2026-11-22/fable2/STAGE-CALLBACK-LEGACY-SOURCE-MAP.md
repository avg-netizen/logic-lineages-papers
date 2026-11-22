# Paper 17: the existing typed alternatives meet the supplier interface

Key: `STAGE-CALLBACK-LEGACY`. Targets module
`LogicLineages.PermittedControl.StageCallbackLegacyTargets`.

Purpose: a check on the hypotheses of `STAGE-CALLBACK-SUPPLIER`, not a new piece of mathematics.
The interface there offers the supplier the raw row majorant and asks for a row-level iff. If no
list could satisfy it, the generic contract would be vacuous. This key shows the accepted typed list
does.

## What is stated

`legacy r top row := ActualPaidMixedMatrixTuples.alternatives r top (compileRow row)`.

- `ExactLegacySupplierShape` — its packets are prepared inputs.
- `ExactLegacySupplierExact` — for every selected control with threshold, `SupplierExact f B legacy`.
- `ExactLegacyLiteralCompile` — as ordered lists, `packets legacy = highPackets` and
  `compile legacy = ActualNamedBitFamilyHighAbove.compile`. So the generic compiler specialises to the
  accepted one exactly, not up to permutation.
- `ExactLegacyStageCallback` — `HighAtStage f B high (stageChildren legacy B)` for every raw program
  with `Emits legacy B high`.

## What is assumed

`SelectedWithThreshold f B`, and for the last target the emission equation.

## What is not claimed

- No computable `high` with `Emits legacy B high` is exhibited, and none is expected: `legacy` is the
  old `Finset`-ordered route list. This key does **not** close the callback.
- Nothing about the canonical executable candidates.
- The last target is the stage contract for the *old typed* list; it restates #1309 + #1336 in the
  `HighAtStage` form and adds no semantic content beyond them.
