# Local Fable-trio continuation — 27 November 2026 — handoff

Release: [RELEASE.md](RELEASE.md). Rules: [BRIEF.md](BRIEF.md). Ledgers: [root](root/LEDGER.md),
[Fable A](fableA/LEDGER.md), [Fable B](fableB/LEDGER.md). Evidence: [evidence/](evidence/) and the lane
directories. Worktree: `logic-lineages-papers-formalization-2026-11-25`, branch
`formalization/paper16-continuation-2026-11-25`, baseline `7c416c4be` plus the coordinator's uncommitted
work of 26 November.

Register unchanged: **161 checked / 6 pending**, all Paper 16. No promotion, no manuscript change, no Git
operation. Every result below is a native gate through `scripts/check.py` (Mathlib profile) with
`propext`, `Classical.choice`, `Quot.sound` only.

**Added 23:05, after the pause:** the owner asked for a way to run the checker on the ThinkPad
([verification/remote-thinkpad/README.md](../remote-thinkpad/README.md)). Its set-up test compiled Fable A2's
three pending modules on the first attempt, so **`AllTowerCalibration` is a theorem**
(`ActualCalibrationAll.allTowerCalibration`, receipt `1795842164430545753-2237658`, standard axioms;
[evidence](evidence/P16-ALL-TOWER-CALIBRATION-EVIDENCE.json)). The cited calibration is no longer an input:
the ordinal statements now need accessibility, the one cited inequality `β ≤ ψ_B(ε_{Ω+1})`, and (for the
printed ordinal name) the endpoint identification. The two-line corollaries that drop the calibration
premise from `exact_HeightFromInputs` / `exact_PrintedFromInputs` are not written (round paused). Fable B3's
eight modules are still uncompiled.

**Round paused on the owner's instruction, 27 November 21:32 (UTC−6).** All lanes are stopped. From about
20:14 the machine's free memory stayed under the checker's 2048 MiB floor (other sessions' processes; swap
full), so the last modules of both lanes were written but never compiled, and no consolidated end-of-round
gate was run. They are listed under "Written, not compiled" below; nothing in this file counts them as
results.

## What the pending statements rest on after this round

**Ordinal side** (`thm:upper`, `lem:tower-cofinality`, `thm:height`, `thm:main`).
`Paper16OrdinalAssemblyProof.exact_PrintedFromInputs` (receipt `1795773740486897347-921184`): at an
independently specified ordinal, the four printed statements follow from exactly

1. the cited norm theorem at that ordinal,
2. `UniformAccessibility` (`lem:arithmetic-accessibility`),
3. `AllTowerCalibration` (pointwise calibration on the actual collapse),
4. the identification of the collapse endpoint with that ordinal.

`OrdinalSemanticsExistence` and `CofinalityAtActualEndpoint` hold outright (same receipt).

Inputs 1 and 4 shrink to one inequality. `Paper16LeastNormBoundProof` / `…HeightProof` (receipt
`1795773771088627501-921381`): the least ordinal β with the norm property exists for the repository's
formal calculus (from its checked soundness; β ≤ ω₁); `thm:upper` at β needs accessibility only; and
accessibility with calibration gives `ψ_B(ε_{Ω+1}) ≤ native height ≤ descending height ≤ β`. So the printed
equalities need, from the literature, exactly `β ≤ ψ_B(ε_{Ω+1})`. Whether the formal calculus is the ID₁ of
the cited source is a correspondence question these modules do not address.
Source maps: [root/P16-ORDINAL-ASSEMBLY-SOURCE-MAP.md](root/P16-ORDINAL-ASSEMBLY-SOURCE-MAP.md),
[root/P16-LEAST-NORM-BOUND-SOURCE-MAP.md](root/P16-LEAST-NORM-BOUND-SOURCE-MAP.md).

**Calibration** (input 3). Instances n = 0, 1, 2 were theorems before; **n = 3 and n = 4 are now theorems**,
and the whole calibration is reduced to two per-level statements, proved at levels 1 and 2.

- `ActualCalibrationThree.psiPowerLevel` (T4, frozen statement unchanged; receipt
  `1795777954162083312-941567`) and `calibrationThree` (T5; receipt `1795777959277796293-941615`) — Fable A,
  with T5 obtained through root's reduction below.
- `CollapseDiagonalProof.exact_DiagonalCollapse` (receipt `1795774851746846294-928024`): the step from one
  tower level to the next, over abstract collapse data — if `ψ(p e) = L e` along a family of indices below
  the next tower argument, then ψ there is the least fixed point of `L` above the base value.
  [Source map](root/P16-COLLAPSE-DIAGONAL-SOURCE-MAP.md).
- `ActualCalibrationThreeReductionProof.exact_ThreeFromPower` (receipt `1795775278159634077-930287`):
  `LevelFacts → PsiPowerLevel → CalibrationThree`.
- `ActualTowerIndexProof.exact_TowerIndexFacts` (receipt `1795775361523897970-930823`): the index-side
  hypotheses of the diagonal step at every tower level.
- `ActualCalibrationLevelsProof` (receipt `1795778069541429314-942177`): `exact_DiagonalUnfolding`
  (`Δ_{l+2}'` is `fix` of the level diagonal at `Γ_0`, every `l`), `exact_CalibrationStep`, and
  `exact_AllFromLevels`: **`AllTowerCalibration` follows from `LevelFactsAt l` and `PsiTowerLevelAt l` for
  every `l ≥ 1`.** For `l = 1` these are Fable A's theorems; for `l ≥ 2` they are open, and it has not been
  checked that they are true as stated. Fable A's [level note](fableA/LEVEL-L-NOTE.md) argues on paper that
  the level-2 statement is true as written and sets out a uniform induction (a logical relation by type
  level with one analytic lemma). Level 1 is bridged to this interface (`ActualCalibrationLevelOneProof`,
  receipt `1795778199692925204-942837`).
- `ActualCalibrationLevelsLimitProof.exact_LevelDiagonalLimit` (receipt `1795812933152467877-1085623`): the
  limit conjunct of `LevelFactsAt l` holds at every level.

**Accessibility** (input 2): Fable B's lane — see its section below.

## The coordinator's pending drafts

Every root named as pending in the three 26 November handoffs was put through the gate
([root/CODEX-DRAFT-GATE-RESULTS.md](root/CODEX-DRAFT-GATE-RESULTS.md) has each receipt). Sixteen roots
pass as written. Three fail on one-line defects; each repair is verified on a renamed copy:

| File | Defect | Repair | Applied to original? |
| --- | --- | --- | --- |
| `LogicLineages/PersistentMarking/NumberedWindowInternalLiteralJoinedBetaOutcomeProof.lean` | `eqn` not in the `open` list (line 18) | add `eqn` | **yes** — it blocked `…InstalledLambdaWindowV2` and four more roots that Fable B's assembly needed; pre-edit copy in `drafts/root/` |
| `LogicLineages/PersistentMarking/NumberedWindowInternalLiteralBetaBoundIndexProof.lean` | two `private theorem`s return a `Derivation` (data) | `private def` | no |
| `LogicLineages/NativeModule/PersistentMarking/Paper16AccessibilityMilestoneBetaLambdaConsumerProof.lean` | `ID1Completion.InternalCalculus` not opened | add the `open` | no |

The three `…RepairCheckProof` modules exist only as proof that the repairs suffice.

## Fable A — ordinal calibration

All gated, every gate first attempt ([ledger](fableA/LEDGER.md), [evidence](fableA/)):

- n = 3: `psiPowerLevel` (T4, frozen statement unchanged, receipt `1795777954162083312-941567`),
  `calibrationThree` (T5, receipt `1795777959277796293-941615`). The round-6 plan's closed formula for
  ψ on `[Ω, Ω^Ω)` and its normal-form recursion were not needed: the proof is two one-step inequalities
  about an arbitrary context (`upperStep`, `lowerStep`).
- A level-independent step calculus: `stepBase`, `stepDiagonal` (the one analytic lemma — the diagonal of a
  family of steps is a step; root's `exact_DiagonalCollapse` is its empty-context case), `stepSuccessor`,
  `stepLimit`, `stepB0Orbit` (receipts `1795813154779391068-1086911`, `1795813329715669451-1087857`,
  `1795813662649156533-1089665`). [Source map](fableA/STEP-CALCULUS-SOURCE-MAP.md).
- Level 2: `levelFactsAt_two`, `psiTowerLevelAt_two`, **`calibrationAt_four`** (receipt
  `1795814433033321726-1094148`).

Open: levels l ≥ 3, i.e. the uniform induction over the type level
([plan](fableA/LEVEL-L-NOTE.md); level 2 corrected two of its side conditions, recorded in the ledger).
Fable A's session was retired for length; a fresh session, **Fable A2** ([ledger](fableA2/LEDGER.md),
[plan](fableA2/UNIFORM-INDUCTION-PLAN.md), [source map](fableA2/UNIFORM-SOURCE-MAP.md)), took the uniform
induction:

- Gated, every type level: `towerGood` / `orbitGood` (function side; receipt `1795815845408612238-1101794`),
  `familyDiagonal` (receipt `1795815470684857486-1099377`), `familyLifting` and the base families (norm
  side; receipt `1795816095108793665-1103069`).
- **Written but never compiled** (the machine's free memory stayed under the checker's floor from about
  20:14): `ActualCalibrationUniformWeightProof` (`orbitWeight`, `towerWeight`),
  `ActualCalibrationUniformLevelProof` (`allLevels`), `ActualCalibrationAllProof` (`allTowerCalibration`,
  `calibrationAt_five`). **`AllTowerCalibration` is not a theorem yet.** No mathematical blocker is known;
  the lane found one new side condition on paper at level 3 (`|s| ≤ |s+1|`, carried by its chain
  condition). To continue: run the gate command in `fableA2/LEDGER.md` Entry 6 and repair elaboration
  errors in the order Weight, Level, All.

## Fable B — internal accessibility

First return (all gated): `exact_FinishMultisets` (the frozen V2 target; receipt
`1795773714932362718-921018`); `exact_InstalledAccessibilityReduction` (receipt
`1795774776803253954-927590`): for every closed K there is one installed window on which
`FreshApplicationTotal → CarrierTypingCases` and
`CarrierTypingCases → TypedCarrierComputability → AllTerms`, with no `ApplicationArithmetic` premise;
`exact_GroundUniverseReduction` (receipt `1795774915562672368-928420`). Open:
`FreshApplicationTotal` ([report](fableB/FRESH-APPLICATION-REPORT.md)) and `TypedCarrierComputability`.

Second return (all gated): `exact_FreshApplicationFromLeast` (receipt `1795775517562288460-931660`):
K1 → K2 → `FreshApplicationTotal`, where K1 = `FreshAddressCarrier` (the selected fresh address is a scalar
carrier) and K2 = `FreshSeedLeast` (the installed least program returns a successor on the application
seed); `exact_LiteralWindowSelection` (receipt `1795778131763821298-942489`): for every closed K one window
with literal probe leaves carrying the joined beta rules and both reductions. **On that window
`lem:arithmetic-accessibility` rests on K1, K2 and `TypedCarrierComputability`.**

Blocker for K1/K2 ([report](fableB/SEED-MEMBER-REPORT.md)): they need "a seed occurs in its own cover pool",
and the cover's syntax program and measure are existential witnesses
(`NumberedWindowInternalFactoredCoverNumericProof.selected`), so no open-term law about them is derivable —
the round-6 opacity obstacle. The other half, pool occurrence ⇒ successor output of the least program
(`SeedMemberLeast`, frozen), is visible code and only unwritten.

Third return (gated, receipt `1795778392935152296-943657`): `exact_LiteralWindowWithLeast` — the selected
window also exports the code of its least program and `MemoSelectedReports`.
[Scope report](fableB/EXPLICIT-COVER-SCOPE.md): the cover's generator is explicit; syntax and measure are
visible wrappers around opaque Primrec-realized leaves. **K2 needs no explicit program** (its seed is an
auxiliary node): it needs `SeedMemberLeast` and two auxiliary-node introduction laws. **K1 is the opacity
case**: root checked the wrappers ([finding](root/K1-VARIABLE-NODE-FINDING.md)) — they intercept only
auxiliary rows, so a variable payload is decided by the opaque leaf; the smallest repair is a visible
front test for variable nodes with all-input calibration preserved.

Fable B's session was retired for length. A fresh session, **Fable B2** ([ledger](fableB2/LEDGER.md)):

- `exact_SeedMemberLeast` (receipt `1795813243959391076-1087336`), a corollary of an accepted legacy theorem.
- **K2 is a theorem**: `exact_LiteralWindowWithSeedLeast` (receipt `1795813935784752720-1091243`) — a
  selection that also exports the rank/type guards, on whose window `FreshSeedLeast A c` holds for every
  `c`. This window supersedes the earlier ones. **On it `lem:arithmetic-accessibility` rests on K1
  (`FreshAddressCarrier`) and `TypedCarrierComputability` only.**
- **K1 is a theorem**, by installing visible front tests for variable nodes on the three opaque leaves
  (syntax, window, measure) and re-selecting the packet there: `exact_FreshCarrierOnFrontWindow` and
  **`exact_FrontLiteralWindowTyping`** (receipt `1795815925311427086-1102198`): for every closed K one
  installed window on which `CarrierTypingCases` holds outright and
  `TypedCarrierComputability A c → AllTerms A c`. **`lem:arithmetic-accessibility` now rests on
  `TypedCarrierComputability` on that window alone** (the paper's neutral lemma, lambda fact, constructor
  induction and structural induction). Caveat: `FrontPacketV2` is generated from the coordinator's
  uncommitted `NumberedWindowInternalLiteralLambdaJoinedMemoPacketProof`; if that file changes it must be
  regenerated and its gates rerun.

B2's session was retired for length. A fresh session, **Fable B3** ([ledger](fableB3/LEDGER.md)), mapped
`TypedCarrierComputability` row by row on that window:
[fableB3/TYPED-COMPUTABILITY-MAP.md](fableB3/TYPED-COMPUTABILITY-MAP.md). **Nothing of B3 is compiled.** Its
reading: the neutral lemma, bottoms, free variables, application inversion, "computability ⇒ I" and the
applied-lambda rule already exist and need only instantiation at the window; bound variables, lambda step
inversion, substitution/step commutation, constructor step exhaustion and the carrier shape split are
blocked on opaque program witnesses (`leaves`, `other`, `seed`, `H`, `base₀`, `V₀`) — and front tests cannot
supply the two that need the content of the rewrite rules; the structural induction under substitution has
no internal statement yet. Finding: the frozen `ApplicationEdgeMatching` is not derivable as stated (no
carrier premise on the edge's source); nothing downstream consumes it.

## Written, not compiled

No receipt exists for any of these; treat them as drafts. Module prefix
`LogicLineages.NativeModule.PersistentMarking.`

| Lane | Modules | Would give | How to continue |
| --- | --- | --- | --- |
| Fable A2 | *(compiled 23:05 on the ThinkPad — no longer in this table; see the note at the top)* | — | — |
| Fable B3 | `Paper16AccessibilityMilestone{TypedRows,GeneralSeedLeast,ApplicationResult,FrontRows}{Targets,Proof}V2` | neutral facts and the beta application at the window; `TypedCarrierComputability` from four named rows; K2 for arbitrary carriers; typing of application results | three gates in the order given in `fableB3/TYPED-COMPUTABILITY-MAP.md` §3.2 |


## For the owner

- Nothing is committed. New files only, apart from the one-token repair above.
- **Accessibility design decision** (from Fable B3's map): the remaining rows of
  `TypedCarrierComputability` need the raw rule checkers and substitution leaves (`leaves`, `other`, `seed`,
  `H`) as explicit programs in one more packet re-selection; front tests, which sufficed for K1, cannot give
  constructor step exhaustion or substitution/step commutation. Whether to write those programs is the
  next decision on that line.
- Lean gates can now run on the ThinkPad (`verification/remote-thinkpad/tp.sh gate …`), which has the memory
  this host lacked. First things for a resumed round: Fable B3's three gates (order in its map §3.2), and
  the corollaries dropping the calibration premise from the ordinal assembly.
- Two verified one-line repairs wait to be applied to the coordinator's drafts (table above).
- `lem:realization` needs one sentence reworded and nothing else: proposal with the exact replacement in
  [root/P16-REALIZATION-WORDING-PROPOSAL.md](root/P16-REALIZATION-WORDING-PROPOSAL.md). Accepting it would make the
  register 162 / 5. Not applied.
- No statement was promoted; whether any of this round's conditional statements should be recorded as
  numbered supporting records is left to the owner or the coordinator.
