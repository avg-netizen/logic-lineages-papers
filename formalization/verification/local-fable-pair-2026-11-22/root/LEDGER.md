# Root ledger (Paper 16 lane + coordination) — 2026-11-22

Times are local UTC−6.

- 15:05 Fetched; fast-forward `d91f1a1da` → `1bd0f9d9a` (628 commits, clean tree). Policy lifted, prior archived.
- 15:14 Cache warmer started for the P16/P17 frontier closures (107 + 238 uncached modules).
- 15:16 Fable-2 smoke turn 000 ok (API key route, no fallback); turn 001 launched (Paper 17 lane).
- 15:19 **Frozen** `LogicLineages/PersistentMarking/NumberedWindowInternalCoverCombinedRestrictedPairedMinimumTargets.lean`
  sha256 `0c209e3d1b5e3a294c4dffec3797148b9057dddac0b2a3efd646e3287a5a0082`
  (three statements: `…PairedEdge`, `…PairedEdgeMinimum`, `…PairedParentMinimum`).
- 15:21 **Gate PASS** `…PairedMinimumProof`, receipt `1795382347539116427-3134146`, all three theorems
  `[propext, Classical.choice, Quot.sound]`.
  Observation: the 22 Nov handoff planned to reach equal minima through mutual inclusion of the
  reached pools (`exact_MembersSeedInclusion`) and the packed lower bounds. That detour is not needed:
  accepted #818 `exact_MutualEdgeMinimumEquality` holds for every `guardedExchange C s baseX` and every
  window, with no cover/pool/length input, and the combined restricted paired exchange is literally of
  that form. The paired cross-cover theorem (#1379) supplies the edge in both directions because its
  hypotheses are symmetric in f and g.
- 15:31 Supporting record **#1386** written (`accepted/1386-p16-combined-paired-parent-minimum.json`, evidence under `evidence/`). Opus A (P16 common least + shared measure) and Opus B (P17 join regression + S4 survey) launched 15:30.
- 15:39 Fable-2 turn 001 returned (session `4a3a4da0-cdde-4bbc-ae02-9b57d0637386`, API key route, no fallback, $12.06):
  `STAGE-CALLBACK-SUPPLIER` receipt `1795383321915397551-3140006` (7 aliases) and `STAGE-CALLBACK-LEGACY`
  receipt `1795383385993393338-3140433` (5 aliases). Root scope check: `ExactSuppliedStageCallback`
  concludes the unchanged `OriginalPrintedRawStageQuery.HighAtStage` of #1372; its only hypotheses are
  `SupplierShape`, `SupplierExact` and the literal emission equation `Emits`; the legacy record shows the
  interface is inhabited for every selected control. Source hashes re-verified against the lane evidence.
  Records **#1387**, **#1388** written. Turn 002 launched 15:41 (canonical supplier).
- 15:45 Opus B returned. `JOIN-REGRESSION` receipt `1795383497904313310-3141177` (regression TRUE, all controls);
  root read the frozen Targets: the statements are on the accepted `tuplePacket`/`project`/`lowerFamily`,
  not a toy copy. Record **#1389** written. Its compile probe for the survey was moved out of the Lean
  tree to `opusB/probes/…Probe.lean.txt` (receipt `1795383773241033889-3145032`; not a target).
  Survey `opusB/S4-SURVEY.md`: (1) `properClauses` is the one emission step with no raw counterpart
  (operand half `ProperField` has no code-level decider); (2) only `eliminatePreparedCode` (#728) has a
  code-level program among packet operations, the rest are typed-computable but uncoded, no
  `Primcodable` for `LowerOperand`/`ValueField`/`NONote`; (3) nothing after the supplier depends on the
  legacy Finset order.
- 15:50 Opus A returned; hashes re-verified. Records **#1390** (common least, receipt `1795383502273947273-3141179`),
  **#1391** (shared-measure equality + parent, `1795384092628823605-3146358`), **#1392** (edge + common least at
  function-level measure, `1795384163800122757-3146619`). Findings kept: #858 does not apply to the combined
  programs' `sharedMeasure`; the directed exchange has no measure guard, so some measure hypothesis must be
  supplied (the older route's `measuredExchange` had one); existence of leasts comes from #1338.
- 15:46 Opus B resumed on task 3: raw decider for `properClauses` (prefix `RawProperClause`).
- 15:58 Opus B task 3 returned: raw proper-clause decider, receipt `1795384636944616848-3148397`, record **#1393**. Filter stays in `packets`; codes are injective; correctness only on encoder outputs.
- 15:58 Fable-2 turn 002 returned (same session, API key route, no fallback; session total $23.13, about $11 this turn):
  `STAGE-CALLBACK-CANONICAL-ROUTES` receipt `1795384393687194447-3147472` (10 aliases) and
  `STAGE-CALLBACK-CANONICAL-SUPPLIER` receipt `1795384564796366985-3148105` (4 aliases). Records **#1394**,
  **#1395**. The canonical supplier meets the turn-001 `SupplierExact` unchanged, so
  `HighAtStage f B high (stageChildren canonical B)` holds for every raw program with `Emits`.
  Remaining for the closed-block decision theorem: the raw program (level-order supplier with an activity
  test, raw guard rendering, raw packet algebra, the #1393 filter) and the close step.
  Opus B on task 4 (raw packet algebra, prefix `RawPacketAlgebra`).
- 16:03 Root: **frozen** `ClosedBlockDecisionTargets.lean` (sha `56edf930…c1fb0`), **gate PASS** `ClosedBlockDecisionReductionProof` receipt `1795384822781080370-3149287`, record **#1396**. `thm:arithmetic` comparator reduced to `ComputableEmitter` at the two controls; comparator correspondence unreviewed (see source map).
- 16:13 Fable-2 turn 003 returned (session total $32.08, about $9 this turn; API credits, no fallback):
  `STAGE-CALLBACK-LEVEL-ORDER` receipt `1795385070227028433-3150794` (7 aliases) and
  `STAGE-CALLBACK-RAW-LEVEL` receipt `1795385515892315614-3152703` (5 aliases). Records **#1397**, **#1398**.
  #1398 is conditional on `Rendering.Exact` (four rendering programs, each one calibration equation).
  `levelOrder` is the supplier for the close step (#1396's `ComputableEmitter`).
- 16:17 Opus A task 3 returned; hashes re-verified. Records **#1399** (round induction with application
  motive), **#1400** (combined programs under `MeasurePreservingEdge`), **#1401** (measured exchange
  preserves measure), **#1402** (least representative, generic), **#1403** (least representative on the
  combined programs; premise-free over the measured exchange). Open design point for the owner/next round:
  whether the combined route should install the measured exchange (the measured analogue of #1377 is the
  missing single-exchange piece; route written in Opus A's report and ledger).
- 16:20 Opus B task 4 returned: raw packet algebra groups 1–5 gated; records **#1404–#1408** (join, guard, residual, reify, child). New code `encodeResidual` (tuple of existing codes, internal to `childCode`). No shape hypothesis anywhere.
- 16:26 Fable-2 turn 004 returned (session total $41.84, about $10 this turn; API credits, no fallback): `STAGE-CALLBACK-RENDER-LINEAR`
  receipt `1795385975542327937-3154727`, `STAGE-CALLBACK-RENDER-MODULAR` receipt `1795386238420603404-3156069`.
  Records **#1409**, **#1410**. `Rendering.Exact` fields: append (Opus B #1404), linear, modular gated; guard open.
  Opus B stopped task 5 (congruence) without writing anything because Fable-2 had it; reassigned to the guard rendering.
  Fable-2 held until Opus A (emitter assembly) and Opus B (guard) return, to avoid a duplicate paid turn.
- 16:40 Correction: receipt `cost_usd` is the session's running total. Fable-2's four turns cost $41.84 in all,
  not the sum of the four figures. Owner: $32 left on the API key; hand off to **fresh sessions with narrow
  briefs** from now on (no `--resume` of session `4a3a4da0…`).
- 16:36 Opus A task 4 returned: stage emitter gated in five modules, records **#1411–#1415**. `exactClosedBlockDecisionFromGuard`: `ClosedBlockDecision` from one guard program with `GuardExact` and `GuardEffective`. Fresh Fable-2 session F01 (P16 measured paired step) launched 16:42.
- 16:37 Opus B task 6 returned: guard rendering receipt `1795386947138244103-3158617` (record **#1416**), concrete record `R₀` exact and effective receipt `1795386972428225726-3158838` (record **#1417**). Opus B resumed to gate the one-line close `closedBlockDecision : ClosedBlockDecision`. Opus A on task 5 (thm:arithmetic correspondence table, thm:ground gap map; reading only).
- 16:38 **`closedBlockDecision : ClosedBlockDecision` gated, no hypothesis**, receipt `1795387043908318394-3159191`, record **#1418** (supporting; candidate for numbered `thm:arithmetic`, not promoted — comparator correspondence is the owner's decision; Opus A writing the correspondence table).
- 16:43 Fresh Fable-2 session F01 returned ($3.30, API credits, session `2a961804…`): measured paired edge receipt `1795387172641849865-3159773` (**#1419**), measured common least receipt `1795387310118722126-3160624` (**#1420**). Fable-2 total so far $45.32 (4 resumed turns $41.84, smoke $0.18, F01 $3.30).
- 16:50 Opus A task 5 (reading): `opusA/P17-THM-ARITHMETIC-CORRESPONDENCE.md` — verdict: the comparator is the printed
  `thm:arithmetic` in the paper's flattened matrix language, with four named conventions (matrix linear in circuit
  nodes; universal blocks over successful runs; correctness only on admitted encodings; sharing carried by the
  statement's form). `opusA/P17-GROUND-GAP.md` — `thm:ground` is assembly only (M1–M5); `thm:main` = `thm:ground`
  + #339 + #010. Assigned: Opus A M1, M3, M2 (freeze + correspondence table), M5, `thm:main`; Opus B M4 (prefix
  `GroundScalarCircuit`). Fresh Fable-2 session F02 (fully measured round, P16) launched 16:45.
- 16:47 Fresh Fable-2 session F02 returned ($1.98): fully measured edge step, round and representative, receipt `1795387581939296076-3161890`, record **#1421**. Fable-2 total $47.30.
- 16:48 Root: frozen `…MeasuredClassApplicationTargets` (sha `1cb10ccf…9c6b`), gate PASS receipt `1795387703209717105-3162428`, record **#1422** (class-level application congruence over the measured exchange).
- 17:05 Opus B task 7 (M4) returned: `GroundScalarCircuit*`, bundle receipt `1795388649799408449-3165892`, record **#1423**; frozen to Opus A's `GROUND-INTERFACE-FOR-M4.md` verbatim.
- 17:07 Opus A task 6 returned: **`groundComparison : GroundComparison`** and **`mainComparison : MainComparison`** gated with no hypothesis, receipt `1795388718263284980-3166116`. Records **#1424–#1429**. Correspondence tables `opusA/P17-THM-GROUND-CORRESPONDENCE.md`, `opusA/P17-THM-MAIN-CORRESPONDENCE.md`. Register not touched.
- 17:07 Consolidated gate over all 108 new modules: rc 0, every module a verified cache hit, receipt `1795388841702636941-3166500` (log `logs/final-consolidated-gate.txt`). 44 records #1386–#1429, source pins re-hashed: no mismatch. No sorry/axiom/native_decide in new sources. Policy re-paused (round policy archived as `ROUND-LOCAL-RUN-POLICY.json`).
