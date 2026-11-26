# Paper 17: the high callback contract, generic in the per-row packet list

Key: `STAGE-CALLBACK-SUPPLIER`. Targets module
`LogicLineages.PermittedControl.StageCallbackSupplierTargets`.

Printed source: `17-permitted-control-canonical-comparison/sections/arithmetic.tex`,
`thm:arithmetic`, the paragraph "On the all-large branch … Apply effective Presburger elimination to
∃z, treating all lower-input fields as parameters … The resulting formula is in the same matrix
language on n−1 coordinates." Handoff item: "use the checked Cartesian packet evaluation and
chosen-route projection at one shared greatest value and one tied lower table; reify the guarded
residuals as strictly smaller families of the same encoded type; prove both directions of the high
callback contract at the executable stage bound."

## What is stated

A *supplier* assigns to each literal bit row, at a width and a greatest rank, a finite list of
prepared packets. Two properties are asked of it:

- `SupplierShape`: every packet is a prepared input.
- `SupplierExact f B`: for an admitted row, a strictly ordered lower valuation, row ranks inside the
  chart, every lower rank and the greatest value `z` at least the row's own executable majorant
  `rowBound B r (encodeBitRow row)`, and `z` above the preceding rank — the row holds at the updated
  valuation **iff** one of its packets holds at that same `z` with its own tied lower table.

From such a supplier the module builds, with the existing generic operations only, a compiler:
per proper clause the Cartesian choice of one packet per row joined by `tuplePacket`; the symbolic
predecessor guard; projection of the greatest coordinate, decoding, and the lower-chart reification;
one child per valid chart of the family's names.

Targets:

- `ExactSuppliedPacketShape`, `ExactSuppliedRankedPoint` — the joined packets are shaped, and at one
  shared greatest value the ranked family holds iff one joined packet holds.
- `ExactSuppliedUniformChartChild` — a child holds at a lower valuation iff that valuation meets the
  lower chart and some greatest value above the seed gives an all-paid satisfying source valuation.
- `ExactSuppliedHighExistential`, `ExactSuppliedHighDimension` — both directions of "an all-paid
  witness exists iff some child is satisfiable", and every child has strictly smaller dimension.
- `ExactSuppliedStageCallback` — for every exact shaped supplier and every raw program meeting the
  literal emission equation `Emits`, `OriginalPrintedRawStageQuery.HighAtStage f B high
  (stageChildren alt B)` at `stageBound B (encodeFamily fs)` on the executable name list
  `names (encodeFamily fs)`.

## What is assumed

Only the two supplier properties and, for the last target, the emission equation. There is no
hypothesis on `f` or `B` other than through `SupplierExact f B alt`; in particular
`SelectedWithThreshold` is not used by this module. The payments offered to the supplier are the raw
majorant `rowBound`, which is what `stageBound` dominates (through `chartCost` and
`ActualBitFamilyRawRank.familyCode`), not the smaller typed `familyNeed`. This is deliberate: the
canonical route is funded by `inputSignBoundCode`, which `rowBound` contains and the typed cutoff
does not.

## What is not claimed

- No supplier is exhibited here and none is shown computable. (The companion key
  `STAGE-CALLBACK-LEGACY` shows the existing typed alternatives satisfy the interface.)
- No raw high program is constructed; `Emits` is a hypothesis. The compiler `compile` is
  `noncomputable` (it uses `properClauses`, `lowerFamily`, the classical chart filter).
- Nothing about which packets an executable program can emit, about guard rendering, or about the
  canonical candidates. Those are the content of `SupplierExact` for a future supplier.
- No numbered statement is promoted and `thm:arithmetic` is not closed by this.

## Relation to accepted work

The proofs follow `ActualNamedBitFamilyHighAbove{Uniform,Existential,Dimension}Proof` (#1309) and
`OriginalRankedLiteralClauseHighPointProof` step for step, with `highPackets` replaced by the supplied
list and the typed `OriginalSetup`/`highMinimum` payments replaced by the raw majorant. The private
helper lemmas of those modules (`rankReads`, `residualPacket`, `actualChartValues`, `guardedBelow`,
`scopeNamed`, `foldMaximum`) are restated here because they are not exported. No accepted module is
edited.
