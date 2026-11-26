# Paper 17: the canonical per-row supplier meets the stage-callback interface

Key: `STAGE-CALLBACK-CANONICAL-SUPPLIER`. Targets module
`LogicLineages.PermittedControl.StageCallbackCanonicalSupplierTargets`.

Printed source: `17-permitted-control-canonical-comparison/sections/arithmetic.tex`,
`thm:arithmetic`, "On the all-large branch … The order normalization and every pattern guard are
linear in the greatest coordinate z. Current congruences are ordinary Presburger congruences in the
raw coordinates." Handoff: item (a) assembled with items (b) and (c).

## What is stated

`canonical r top row := alternatives r top (compileRow row)` where a signed row receives the
rendered canonical routes of its cleaned syntax at the syntax budget
(`StageCallbackCanonicalRoutes.routes`, rendered by the accepted
`ActualSelectedSignedRoutePacket.packet`) and a congruence row keeps its one accepted packet
(`ActualGreatestCongruenceRoute.packet`).

- `ExactCanonicalSupplierShape` — `SupplierShape canonical`.
- `ExactCanonicalSupplierExact` — for every selected control with threshold,
  `SupplierExact f B canonical`, i.e. the *frozen turn-001 interface unchanged*: admitted row, strict
  lower valuation, ranks in the chart, every lower rank and `z` at least `rowBound`, `z` above the
  preceding rank ⟹ the literal row holds at the updated valuation iff one canonical alternative
  holds at that `z`.
- `ExactCanonicalStageCallback` — hence `HighAtStage f B high (stageChildren canonical B)` for
  every raw program with `Emits canonical B high`.

## What is assumed

`SelectedWithThreshold f B`; for the last target the emission equation.

## What is not claimed

- No computable `high` is exhibited. `Emits canonical B high` is still a hypothesis; this key does
  not close the callback or `thm:arithmetic`.
- `canonical` is `noncomputable` and lists signed alternatives in the depth-first order of the route
  tree. A raw program will most naturally produce a level order. `SupplierExact` and
  `SupplierShape` depend on membership only, so a level-order supplier with the same members
  satisfies them by the same proof; that reordering, and the raw program, are the remaining work.
- Nothing new about congruence rows beyond reusing #1245.

## Interface check

Root asked whether the canonical supplier can meet the frozen interface. It can, with no change: the
extra canonical payment `inputSignBoundCode r (cleanup s).constant (…)` is
`signCode r (encodeSyntax (cleanup s))`, which is below `staticCode B r (cleanupCode (encodeSyntax s))`
(`ActualRawSignedCleanup.cleanupCalibration`), which is the second component of `rowBound` for every
order test. The accepted `LowerSetup` and `replayMinimum` come from the same hypotheses exactly as
for the legacy supplier.
