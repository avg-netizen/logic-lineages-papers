# JOIN-REGRESSION — source map (Opus B)

Targets: `LogicLineages/PermittedControl/ActualSignedRouteJoinRegressionTargets.lean`
(namespace `LogicLineages.PermittedControl.ActualSignedRouteJoinRegression`),
sha256 `3f3c97f6a484f008062cb56b39e29fff459eb649100793a3c24724f0e6a1dbc9`, frozen 2026-11-22T21:34Z
after the Targets module alone compiled (receipt `1795383274001853139-3139721`).

## What it serves

Handoff `verification/continuation-2026-11-22/SESSION-HANDOFF-2026-11-22.md`, Paper 17 "Next":
"A useful join regression is two rows forcing the same greatest coordinate to be the cutoff and the
cutoff plus one; the joined packet must be unsatisfiable." Fable-2's `PLAN.md` ("For Opus B") places
the join at `ActualSignedRouteCartesian.tuplePacket` over `choices`, evaluated at one shared `z` by
`exactCartesianPacketEval`, with projection only after the join, as
`project C (prepend top (tuplePacket …))` inside `ActualGreatestRouteResidual.lowerFamily`.

## The instance

`pinned ops c := (ops, atLeastRow c ∧ atMostRow c)`, where `atLeastRow c` is the literal row
`(-c, [(1, .variable 0)])` and `atMostRow c` is `(c, [(-1, .variable 0)])`, both `.nonnegative`.
Name 0 is the reserved shared greatest coordinate. Row 1 is `pinned ops₁ C`, row 2 is
`pinned ops₂ (C+1)`. Lower tables `ops₁`, `ops₂` are arbitrary in the unsatisfiability statements;
the headline `JoinRegression` uses `[.coordinate k]` with `k < top` in both rows, so the left table is
nonempty and the right packet really is shifted by `append` (a join that also shifted name 0 would
read the right row's `z` from the left table slot, i.e. from `ρ k`, and would be satisfiable at
`ρ k = C+1`; the statement is for every `ρ`, so it would catch that).

Every statement is for every control `f` and every baseline `ρ`. Nothing is re-defined: the
statements use the accepted `tuplePacket`, `choices`, `prepend`, `project` (`eliminatePreparedFormula`
after the cutoff guard), `lowerFamily` (`keep` + `decodeRoute`), `PacketHolds`, `LowerHolds`,
`LowerMatrix`.

## Statements

- `ExactPinnedPacket`: each row packet is `Shape`d and holds at `z` iff `z = c` and its table is tied.
- `JoinedPacketUnsatisfiable`: `tuplePacket [row1,row2]` is `Shape`d, holds at no `z`, and no choice
  from `choices [[row1],[row2]]` holds at any `z`.
- `ProjectedSinglesSatisfiable`: with a tied table, `project C row1` and `project C row2` each hold;
  with `rankedPredecessor top ρ ≤ C`, so do `project C (prepend top rowᵢ)`.
- `ProjectedJoinUnsatisfiable`: `project C (tuplePacket [row1,row2])` and
  `project C (prepend top (tuplePacket [row1,row2]))` do not hold. **This is the check that
  projection after the join keeps the shared-coordinate constraint.**
- `LowerFamilyJoinUnsatisfiable`: for strictly lower tables, `lowerFamily top C [prepend top joined]`
  has length exactly 1 (the joined packet is emitted and decoded, so the next clause is not vacuous),
  and no member satisfies `LowerMatrix`.
- `LowerFamilySinglesSatisfiable`: with tied table and predecessor below `C`, each single row's
  `lowerFamily` has a satisfied residual.
- `CoordinateTableLive`: `[.coordinate k]`, `k < top`, is always tied (non-vacuity of the hypotheses).
- `JoinRegression`: headline, all of the above at `[.coordinate k]`. Hypotheses `k < top`,
  `rankedPredecessor top ρ ≤ C` are jointly satisfiable (e.g. `k = top-1`, `C ≥ ρ (top-1) + 1`).

## Assumed / not claimed

Assumed: nothing beyond the accepted theorems used in the proof (`exactTupleChoice`,
`exactCartesianPacketEval`, `exactChosenRouteProjection`, `exactSymbolicPredecessorAppend`,
`exactSymbolicPredecessorProjection`, `exactDecodedActualResidual`, `exactActualLowerRouteFamily`,
`keepMember`, shape lemmas `safeAtom`/`safeAnd`).

Not claimed: anything about the packets actually emitted for genuine signed rows (`rowPackets`,
`routes`, guards), the canonical supplier, the stage bound, or the high callback contract. The two
rows here are hand-written packets, not outputs of `routes`; the regression tests the join and
projection machinery, which is generic in the packet list.
