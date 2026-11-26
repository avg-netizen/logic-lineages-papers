# Paired common least — source map (Opus A, 2026-11-22)

**Target** `LogicLineages/PersistentMarking/NumberedWindowInternalCoverCombinedRestrictedPairedCommonLeastTargets.lean`,
`ExactOpenCoverCombinedRestrictedPairedCommonLeast`.

**Serves.** Paper 16 frontier, combined restricted paired route: strengthens root's record #1386
(`…PairedParentMinimum`, which *held* the two successful least calls `leastGraph … a x`, `… b y`)
to a statement in which the least calls are *derived*: at the actual chosen programs
`P := combinedPrograms s V TV M M0 B T`, `W := thinMatchingWindow P.cover s P.W P.V`,
`X := guardedExchange P.cover s (thinPairedExchange (directedX base P.V))`, both applications
`a := auxiliaryTerm dom cod f arg`, `b := auxiliaryTerm dom cod g arg` have a successful packed least
and it is one value `x` (continuation style: a fresh `x` with both least calls is handed to the
continuation, which must prove `goal.relabel j`).

**Assumed (exactly the #1386 parent hypotheses, nothing more).** The two type-guard conjunctions at
`dom`, `cod`; `windowAt W ctx dom arg`; the directed parent edges `f → g` and `g → f` at
`rawCons dom cod`; the shared selected measure `m` at `a` and at `b`. No least call, cover report,
pool, length or context-parse report is a hypothesis.

**Suppliers (all accepted).**
- #1386 `exact_OpenCoverCombinedRestrictedPairedEdge` (both directions, by swapping f/g).
- `exact_OpenPackedScalarEdge` (edge ⇒ both window calls `windowAt W ctx cod a`, `windowAt W ctx cod b`).
- #1338 `exact_OpenCoverThinMatchingWindowReport` (generic in `C`, `baseW`, `V`, `X`: a thin matching
  window acceptance gives `hasLeast`; this is where #825 `exact_PackedDomain` and the context parse
  are used — the parse is read off the window's own `thinContextPresent` conjunct, so no extra
  context hypothesis is needed).
- #818 `exact_MutualEdgeMinimumEquality` (equal leasts on mutual edges), `casesLeast`/`hasRename`/
  `leastRename` (packed-domain syntax), `outputTransport`, `congSuc`/`symm`.

**Not claimed.** Nothing about reached pools, lengths, the measure being derivable (task 2), or
uniqueness beyond what the two least calls at one `x` say.
