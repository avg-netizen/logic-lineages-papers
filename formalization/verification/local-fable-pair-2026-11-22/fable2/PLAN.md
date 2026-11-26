# Fable-2 plan — Paper 17, from the supporting results to the high callback contract

Written 2026-11-22 after reading the targets and proofs, not only the notes. Module names are under
`LogicLineages/PermittedControl/`; `X.y` means declaration `y` in namespace
`LogicLineages.PermittedControl.X`.

## Where the gap actually is

The decision theorem is `OriginalPrintedRawSelectedStageQuery.ForControl` (#1372): for every
`high : HighProgram` and `children : TypedHigh` with `OriginalPrintedRawStageQuery.HighAtStage f B
high children`, the raw query is correct, and it is computable when `high` is. So what is owed is

    ∃ high children, HighAtStage f B high children ∧ Computable high.

`HighAtStage` has three clauses per family `fs` of positive dimension, at `C = stageBound B
(encodeFamily fs)`: (1) `high (C, encodeFamily fs) = (children fs).map encodeFamily`; (2) every child
has smaller dimension; (3) `(∃ ρ, AllPaid C fs ρ ∧ Holds f ρ fs) ↔ ∃ ch ∈ children fs, Satisfiable f ch`.

Two things already exist and are easy to overlook:

- A typed, noncomputable compiler with clauses (2) and (3) at any `C ≥ cutoff`:
  `ActualNamedBitFamilyHighAbove.compile`, `exactAboveHighExistential`, `exactAboveHighDimension`
  (#1309), and `ActualRawStageCutoff.exactRawStageCutoffMajorant` (#1336) gives `cutoff ≤ stageBound`.
- Its proofs touch the packet list `OriginalRankedLiteralClauseHigh.highPackets` only through
  `highPacketShape` and `exactRankedLiteralHigh`; everything downstream
  (`ActualSymbolicPredecessorProjection.prepend`, `ActualGreatestRouteResidual.lowerFamily`,
  `ActualGuardedResidualBitFamily.reifyFamily`, `ActualLowerRankChartRows.lowerChart`, the chart
  enumeration) is already generic in a `List Packet`.

So the semantic contract is not missing for the *old* list. What is missing is a list an executable
program can emit. The old one cannot be: `ActualBoundedSignedRoutes.routes` runs on
`normalizedTerms` / `nodePattern` / `successor`, whose order is the legacy `Finset` order (the
"old incidental syntax order" of the handoff). The canonical first-occurrence machinery (#1318–#1384)
is executable (`ActualRawCanonicalZeroPrefixes.prefixes`, `stepCode`, `candidateTapes`), but has only
one direction and no emitted guards.

A second, quieter gap: the canonical results are funded by `inputSignBoundCode ≤ ρ top`
(`ActualCanonicalFundedTerminal`), which is *larger* than the legacy
`terminalCutoffCeiling` (`ActualEffectiveTerminalSignBound.ExactSignBoundDominance` is an inequality
in that direction). The typed cutoff `ActualNamedBitFamilyHigh.cutoff` therefore does not obviously
fund the canonical route; the raw `stageBound` does, because `ActualRawMixedFamilyCeiling.rowBound`
contains `staticCode = max commonCode signCode`. Any interface for the new compiler has to offer the
raw majorant, not the typed need.

## The chain

**S1 — generic contract over a per-row packet supplier (handoff items (b) and (c)).**
For any `alt : Nat → Nat → BitRow → List Packet` with shaped packets and row-level exactness under
the payments the stage bound provides (`SupplierExact`), the compiler built from `alt` by
Cartesian choice per proper clause, predecessor guard, projection at the shared greatest value,
decoding and reification satisfies clauses (2) and (3) of `HighAtStage` at `stageBound`, and hence
`HighAtStage` for every `high` meeting the literal emission equation.
Module `StageCallbackSupplierTargets` (`ExactSuppliedStageCallback` and five supporting targets).
Uses: `ActualSignedRouteCartesian.exactCartesianPacketEval` (one shared `z`, one tied table per
tuple), `OriginalPrintedLiteralRowBridge.exactLiteralProperClauseFilter` / `properClauseMember`,
`ActualSymbolicPredecessorProjection.exactSymbolicPredecessorAppend` / `…Projection`,
`ActualGreatestRouteResidual.exactActualLowerRouteFamily`,
`ActualGuardedResidualBitFamily.exactGuardedResidualUnion`,
`ActualLowerRankChartRows.exactLowerRankChartRows`, `ActualBitFamilyHigh.exactGenericRankTransport` /
`sourceCoordinate`, `ActualNamedBitFamilyHigh.exactNamedCharts` / `renameIndex` / `checkedLength`,
`ActualFiniteOrderBranches.exactActualBranchCoverage` / `exactPatternEnumeration` /
`exactBranchRealization`, `ActualRankChartPrototype.exactChartConsistency`,
`ActualRawStageCutoff.exactRawStageNamesAndCharts`, `ActualBitFamilyRawRank.exactRawRankCalibration`.
No selection hypothesis is needed in S1 itself; `SupplierExact f B alt` carries all of it.
**Attempt first.**

**S2 — the interface is inhabited and loses nothing.** The legacy
`fun r top row => ActualPaidMixedMatrixTuples.alternatives r top (compileRow row)` is a shaped exact
supplier for every selected control, its packet list is literally `highPackets`, and its compile is
literally `ActualNamedBitFamilyHighAbove.compile`. Module `StageCallbackLegacyTargets`.
Uses `ActualPaidMixedMatrixTuples.alternativesShape` / `exactPaidMixedRow` / `exactMixedMatrixMinimum`,
`OriginalPrintedLiteralRowBridge.exactLiteralMixedRowBridge`,
`OriginalRankedLiteralClauseHigh.exactOriginalLiteralReady` on the one-row family,
`ActualRawMixedFamilyCeiling.exactRowBound`. This is a check on S1's hypotheses (that they are not
too strong to meet), not progress toward computability. **Attempt second.**

After S1 the remaining work is exactly two obligations, and they are independent:

**S3 — a canonical executable supplier that is exact (handoff item (a)).** Per signed row, the typed
shadow of the raw candidate list: for each `entry ∈ prefixes (syntaxBudgetCode r start.2) start`,
the packet `guards ++ terminal`, where the guard at each step is
`ActualFiniteFullValueGuards.compile top (pairs (labels terms)) a` on the canonical label order and
the terminal is `ActualCanonicalTerminalTruth.canonicalPacket` (inactive) or the constant truth
value of `signedBit test (maximalCoefficient terms a)` (nonzero). Sub-statements, in order:

- S3a *guard exactness on the canonical order*: under the row payments, `PacketHolds` of the
  compiled guard at `z` iff `Matches f (update baseline top z) (pairs (labels terms)) a`, with a tied
  table always existing. Supplier: `ActualFiniteFullValueGuards.exactFiniteFullValueGuards`
  (already order-parametric in the label list). Missing: `ReadyFamily` / `PaidFamily` for the
  canonical labels of every *reached* state from the row's raw bound — the canonical analogue of
  `ActualGlobalComparisonCeiling.PaidComparisonCeiling`; #1378 has it along one genuine trace.
- S3b *completeness*: a true row has a candidate whose every guard and terminal hold. This is #1384
  (`ActualRawFundedTerminalCandidate.ExactRawFundedTerminalCandidate`) plus S3a at each step of that
  very trace. Needs the valuation `update baseline top z` extended to a `StrictMono` one
  (`ActualRankedNormalizationSyntax.extend`), since the canonical theorems ask `StrictMono ρ`.
- S3c *soundness*: a candidate whose guards all hold is the genuine trace. `Matches` is functional
  in the answer tape (each `ActualOutcome` is a trichotomy), so a holding guard pins the answer to
  the actual one; then `ActualCanonicalZeroTrace.exactCanonicalZeroWitness` and
  `ActualRawCanonicalZeroTraceInclusion.exactActualZeroCandidateEdge` identify the raw step with the
  typed one, and `ActualCanonicalFundedTerminal.exactFundedForwardTruth` gives terminal truth.
  Missing and not yet written anywhere: functionality of `Matches`, and the statement that a
  candidate which *stops* in the raw list (no further step) is at a `StopsAt` node — the raw list
  contains all prefixes, so every proper prefix of a genuine trace is also emitted and must be
  rejected by its terminal; the terminal of a non-stopping prefix has to be falsity, which needs the
  raw node's own active/zero status (`ActualRawCanonicalNode.nodeCode`).
- S3d *congruence rows*: `ActualGreatestCongruenceRoute.packet` and
  `exactGreatestCongruencePacket` already give one exact packet; what is open is whether its
  `layout`/`table` are literal-order (they are `def`, not `noncomputable`, except `packet`) so that
  the raw program can emit it. To check before writing anything.
- S3e *assemble* `SupplierExact f B canonical` from S3a–d, with `rowBound` supplying
  `PaidGlobalTail`, `PaidComparisonCeiling` and `inputSignBoundCode` through
  `ActualRawSignedStaticCeiling` (`commonCode`, `signCode`) and `ActualRawSignedCleanup.cleanupCode`.

**S4 — the emission equation.** A computable `high` with `Emits canonical B high`: raw programs for
`properClauses` (a decidable syntactic filter), `choices`/`tuplePacket`, `prepend`,
`project` (`eliminatePreparedFormula`), `decode`, `reify`/`lowerChart`, the chart enumeration
(`ActualBitFamilyRawCharts.charts` already), and `encodeFamily` of the result. I have not yet checked
which of `project`/`decode` already have a raw computable form; `lowerFamily` and `decodeRoute` are
marked `noncomputable`. This is the part most likely to hide a second "legacy order" problem and
should be surveyed before S3 is finished, so that S3's packet syntax is one S4 can emit.

**S5 — close.** `∃ high, Computable high ∧ HighAtStage f B high (stageChildren canonical B)` from
S1 + S3e + S4, then `ForControl` gives the closed-block decision statement for both controls.

## Order

S1, then S2 (same turn if the gate allows). Next turn: survey for S4 (cheap, reading only) and S3d,
then S3a. S3c is the mathematically riskiest step; S4 the largest.

## Status after turn 002 (addendum; the text above is the turn-001 plan, left as written)

- S1, S2 gated in turn 001. S3 gated in turn 002 as two keys:
  `STAGE-CALLBACK-CANONICAL-ROUTES` (S3a guard exactness, S3b completeness, S3c soundness, for signed
  rows) and `STAGE-CALLBACK-CANONICAL-SUPPLIER` (S3d congruence reuse, S3e assembly into
  `SupplierExact`, and the stage contract for the canonical children).
- Corrections to the plan as written: S3b did not go through #1384's raw inclusion — the typed route
  tree gets completeness directly from the genuine zero witness, because the accepted raw `prefixes`
  ignore `top` and so are not the list the supplier can use. S3c's worry about proper prefixes was
  settled by emitting only stopped candidates. The `StrictMono` and cleaned-syntax risks named in the
  turn-001 ledger were both discharged with accepted lemmas (`contextExtension`,
  `cleanupCalibration`).
- Remaining: S4 (raw program with `Emits`, in level order with an activity test) and S5. See the
  ledger's "State and next (end of turn 002)".

## Status after turn 003 (addendum)

- S4 is now split into named links. Gated: the level-order supplier with its stage contract
  (`STAGE-CALLBACK-LEVEL-ORDER`) and the raw per-row level program calibrated to it, parametric in
  four rendering programs (`STAGE-CALLBACK-RAW-LEVEL`).
- Open, mine: the rendering programs R1 `guard`, R2 `linear`, R3 `modular` with `Rendering.Exact`;
  `Primrec` of `rowCode R`; the final assembly of `high` with `Emits levelOrder B high` and
  `Computable high`.
- Open, Opus B: gated `ExactAppendCode`/`Primrec₂ appendCode`; the residual program
  (prepend, project, decode, reify) as one `childCode` with a literal equation for every packet list.
- The ledger's turn-003 sections give the exact statements and the composition into `Emits`.

## Status after turn 004 (addendum)

- Gated: the linear-exit rendering (`STAGE-CALLBACK-RENDER-LINEAR`) and the congruence rendering
  (`STAGE-CALLBACK-RENDER-MODULAR`), each with its literal calibration (exactly the corresponding
  field of `Rendering.Exact`) and `Primrec`.
- `Rendering.Exact` now lacks only the `guard` field (comparison-guard rendering). After it: assemble
  one concrete `R₀`, effectivity of `rowCode R₀`, and — with Opus B's residual program — `high`,
  `Emits levelOrder B high`, `Computable high`, ending in root's `ComputableEmitter f B` (#1396).

## For Opus B (join regression)

The join in S1 is `ActualSignedRouteCartesian.tuplePacket` over `choices`; "one shared greatest
value and one tied lower table" is `exactCartesianPacketEval` at a common `z`, and projection happens
only after the join (`project` is applied to `prepend top (tuplePacket …)` inside `lowerFamily`).
A regression with two rows forcing the greatest coordinate to be `C` and `C+1` should therefore be
stated on `PacketHolds f baseline top z (tuplePacket [p₁,p₂])` being false for every `z`, and then on
`LowerHolds … (project C (tuplePacket [p₁,p₂]))` being false — not on the two projected packets
separately, which are each satisfiable. `ActualLowerRankChartRows.fundRow` shows the row syntax for
"coordinate ≥ B" (`(.nonnegative, -B, [(1, .coordinate i)])`).
