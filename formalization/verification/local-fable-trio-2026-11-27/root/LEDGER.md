# Root ledger — local Fable-trio round, 27 November 2026 (times UTC−6)

- 03:25 Fetched in the older checkout; found the newer worktree `logic-lineages-papers-formalization-2026-11-25`
  (`formalization/paper16-continuation-2026-11-25` at `7c416c4be`, 67 commits past round 6, plus the Codex
  coordinator's uncommitted work of 26 November). Register there 161 checked / 6 pending. Round home created
  here; no Git operation, coordinator files untouched.
- 03:47 Build cache of this worktree had no objects for the round-6 ordinal modules. Warm gate started on
  `ActualCalibrationThreeLevelProof`, `ActualCalibrationChecks`, `ActualCollapseMainProof`,
  `Paper16RemainingOrdinalTargets` (log `logs/warm-ordinal-1.txt`).
- 03:51 Fable A (ordinal calibration: T4 `PsiPowerLevel`, T5 `CalibrationThree`) and Fable B (internal
  accessibility: one of the three `CloseAllTerms` premises) launched as Fable 5.2 high subagents.
- 03:54 Root lane target frozen: `Paper16OrdinalAssemblyTargets`
  (sha256 `9ff0897575dc18d555322f4cfd562f41bb9f77bda5fd6d2ec45750423acf7818`), source map
  `root/P16-ORDINAL-ASSEMBLY-SOURCE-MAP.md`. Proof drafted in `Paper16OrdinalAssemblyProof` (ten theorems,
  two of them existing targets of `Paper16RemainingOrdinalTargets`: `OrdinalSemanticsExistence`,
  `CofinalityAtActualEndpoint`). Not yet gated.
- 03:59 Second root target frozen: `Paper16LeastNormBoundTargets`
  (sha256 `7b0b5703d61a604556627e04250f14d867c6c4a5de48d6b060e2e75e3c70a411`), source map
  `root/P16-LEAST-NORM-BOUND-SOURCE-MAP.md`. Proofs drafted in `Paper16LeastNormBoundProof` (stage
  exhaustion along countable ordinals, soundness in stage form, `NormTheorem ω₁`, existence and uniqueness of
  the least norm bound) and `Paper16LeastNormBoundHeightProof` (upper bound at it; heights between the
  collapse endpoint and it). Not yet gated. First draft of existence took a supremum over all positive
  bodies; that type lives in `Type 1`, so the bound is taken at `ω₁` uniformly instead.
- 04:01 Warm gate done: rc 0, 697 modules compiled, receipt `1795773062111927905-914623`. It includes the first
  native check of `Paper16RemainingOrdinalTargets` (TARGETS.md listed it as still requiring one).
- 04:02 Gate `1795773740486897347-921184`: `Paper16OrdinalAssemblyTargets` and `Paper16OrdinalAssemblyProof`
  **PASS** (ten theorems, standard axioms), `Paper16LeastNormBoundTargets` PASS; `Paper16LeastNormBoundProof`
  failed on one name (`Ordinal.isSuccLimit_omega`; the lemma is `Cardinal.isSuccLimit_omega`). Failed draft
  kept in `drafts/root/`.
- 04:03 Gate `1795773771088627501-921381`: `Paper16LeastNormBoundProof` (seven theorems) and
  `Paper16LeastNormBoundHeightProof` (three theorems) **PASS**, standard axioms. Evidence:
  `evidence/P16-ORDINAL-ASSEMBLY-EVIDENCE.json`, `evidence/P16-LEAST-NORM-BOUND-EVIDENCE.json`.
- (note) Earlier clock labels in this ledger were estimated and wrong; corrected from file times at 04:05. Old copy: `drafts/root/LEDGER.wrong-clock.md.txt`.
- 04:04–04:08 Gated the Codex coordinator's pending window-lane drafts (never compiled before; sources untouched):
  - `Paper16AccessibilityMilestoneArrowTypedIntroductionV2` (`exact_OriginalArrowTypedIntroduction`) and
    `…RetypedGroundV2` (`exact_RetypedGroundFromCarrierAndResult`): **PASS**, receipt `1795773831011891982-921759`.
  - `…DirectWindowSelectionV2` (`exact_SelectInstalledWindows`): **PASS**, receipt `1795774182715412200-924040`.
  - `…InstalledLambdaWindowV2`, `…GroundWindowTypingV2`, `…RetypedJoinedWindowV2`: **BLOCKED** (receipts
    `1795773845162210392-921826`, `1795774162174855745-923903`) by one dependency, the coordinator's
    uncommitted edit of `LogicLineages/PersistentMarking/NumberedWindowInternalLiteralJoinedBetaOutcomeProof.lean`:
    line 89 `Unknown identifier eqn` — the new `BetaOutcomeWithTypeAt` uses `eqn`, the `open` on line 18 lists
    only `eqnRelabel sucRelabel zRelabel`.
- 04:09 Verified the repair without touching that file: a renamed copy
  `NumberedWindowInternalLiteralJoinedBetaOutcomeRepairCheckProof` whose only other change is
  `open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel zRelabel)` **PASSES**
  (receipt `1795774225006756154-924321`, all four declarations, standard axioms). So the one-token change on
  line 18 of the original is the whole repair. Not applied: the file is the coordinator's uncommitted work.
- 04:10–04:15 Gated twelve more pending coordinator drafts, one root per call: nine **PASS**
  (fixed seed coverage and settings; lambda child window, prefix parent stop, context intro, hop projection;
  bound hit and bound order accepted; leaf syntax supplier), two blocked by the `eqn` defect above, one
  (`NumberedWindowInternalLiteralBetaBoundIndexProof`) fails because two `private theorem`s return a
  `Derivation` (data). Repair `theorem → def` verified on a renamed copy, receipt
  `1795774494332507116-925952`. Table with every receipt: `root/CODEX-DRAFT-GATE-RESULTS.md`.
- 04:18 **One edit to a coordinator file.** Fable B's planned assembly (its PLAN item C) needs
  `Paper16AccessibilityMilestoneInstalledLambdaWindowV2`, which cannot compile while
  `NumberedWindowInternalLiteralJoinedBetaOutcomeProof.lean` (tracked, already carrying the coordinator's
  uncommitted edit) fails on the missing `eqn` in its `open` list. Seven modules sit between the two, so the
  alternative was eight duplicate modules. Applied the verified one-token repair on line 18 (`(eqnRelabel …)`
  → `(eqn eqnRelabel …)`); nothing else in the file changed. Pre-edit copy:
  `drafts/root/NumberedWindowInternalLiteralJoinedBetaOutcomeProof.before-open-fix.lean.txt`. To undo, copy
  it back. This is the only existing `.lean` file this round has modified.
- 04:19–04:24 After the repair: `…InstalledLambdaWindowV2` **PASS** (`1795774571363926080-926371`),
  `…GroundWindowTypingV2` + `…RetypedJoinedWindowV2` **PASS** (`1795774711062968825-927238`),
  `…BetaAddressProof` **PASS** (`1795774722798565966-927293`). `…BetaLambdaConsumerProof` fails on a missing
  `open ID1Completion.InternalCalculus`; repair verified on a renamed copy (`1795774934502289421-928551`),
  original not edited. Every pending coordinator root named in the three 26 November handoffs is now either
  gated or has a verified one-line repair on record (`root/CODEX-DRAFT-GATE-RESULTS.md`).
- 04:20 Told Fable A that root takes the n = 3 reduction `PsiPowerLevel → CalibrationThree`; A stays on T4.
- 04:23 Third root target frozen and proved: `CollapseDiagonalTargets`
  (sha256 `ae17d0cbb5e68181e997df4bc1c3e42a1bf8da5fc258beba61ffec2d47fec13c`),
  `CollapseDiagonalProof.exact_DiagonalCollapse` **PASS** on the first gate, receipt
  `1795774851746846294-928024`, standard axioms. The step from one tower level to the next, over abstract
  collapse data: if `ψ(p e) = L e` along a family of indices below the next tower argument (below the first
  fixed point of `L`), then `ψ` at that argument is the least fixed point of `L` above the base value.
  Source map `root/P16-COLLAPSE-DIAGONAL-SOURCE-MAP.md`.
- 04:25 Fable B returned (first turn). Gated, standard axioms: `exact_FinishMultisets`
  (`1795773714932362718-921018`, the frozen V2 target, for every window); arrow typing by recursion on the
  type from five probe reports plus `FreshApplicationTotal` (`1795774234561241622-924414`); the five reports on
  the stacked literal window and the window reduction (`1795774692720129882-927148`);
  `exact_InstalledAccessibilityReduction` (`1795774776803253954-927590`): for every closed K one installed
  window with `FreshApplicationTotal → CarrierTypingCases` and
  `CarrierTypingCases → TypedCarrierComputability → AllTerms` (no `ApplicationArithmetic` premise);
  `exact_GroundUniverseReduction` (`1795774915562672368-928420`). No ungated drafts. Open:
  `FreshApplicationTotal` (report `fableB/FRESH-APPLICATION-REPORT.md`), `TypedCarrierComputability`.
  Resumed on the reduction of `FreshApplicationTotal` to two least-program totality facts and the
  seed-membership law.
- 04:28 Fourth root target frozen and proved: `ActualCalibrationThreeReductionTargets`
  (sha256 `c337e4be3c638ff4feded5d2ecb0aa13f87d64f95dc7fa6779e3159c1e1f12e7`),
  `ActualCalibrationThreeReductionProof` **PASS** on the first gate, receipt `1795775278159634077-930287`,
  standard axioms: `exact_PowerIndexFacts` (Ω^e < Ω^Ω; |Ω^e| ≤ e; η < Ω^Ω with |η| < e lies below Ω^e),
  `exact_ThreeFromLevelFacts` (the n = 3 instance at one solution from `LevelZeroStrict`,
  `BaseBelowLevel` and T4 there, by `exact_DiagonalCollapse`), `exact_ThreeFromPower`
  (`LevelFacts → PsiPowerLevel → CalibrationThree`). So T5 now needs exactly: T4 (Fable A) and the two
  facts about L (strictly increasing; Γ_0 < L e for e ≥ 1), which Fable A's hierarchy module plans as
  `levelZero_strict` and `base_lt_level`. Evidence `evidence/P16-CALIBRATION-THREE-REDUCTION-EVIDENCE.json`;
  the source map is the "Statement" section of `root/P16-COLLAPSE-DIAGONAL-SOURCE-MAP.md` plus the targets
  module's header.
- 04:29 Fifth root target frozen and proved: `ActualTowerIndexTargets`
  (sha256 `ca04b9f1a90be39d061abf8b6bc0cb26dbbf5b223b9c1e20307e6f2c2b7ed52a`),
  `ActualTowerIndexProof.exact_TowerIndexFacts` **PASS** on the first gate, receipt
  `1795775361523897970-930823`, standard axioms. For every level k: the index
  `towerIndex k e` (e, Ω^e, Ω^Ω^e, …) lies below a_{k+2}, has norm ≤ e, and bounds every index below
  a_{k+2} of norm < e. These are the `below` / `norm` / `cover` fields of the diagonal step at every
  tower level (k = 1 is the n = 3 case), so the ψ-side bookkeeping of the general calibration step is done;
  what a level needs beyond it is its own T4 and the two facts about its diagonal.
- 04:35 **Round stopped: the user's usage limit was reached.** Both Fable lanes stopped by root mid-turn (not
  by their own choice). State at stop — Fable A: gate 1 passed (`1795775348133540559-930683`: PsiTargets,
  HierarchyProof incl. `levelZero_strict`, `base_lt_level`; CriticalProof); UNGATED drafts
  `ActualCalibrationThreeNormProof.lean`, `ActualCalibrationThreePsiProof.lean`; `exact_LevelFacts` not yet
  written (three lines from its two lemmas; then T5 = T4 only). Fable B: first return fully gated; second
  turn (reduction of `FreshApplicationTotal` to two least-program totality facts) interrupted — read
  `fableB/LEDGER.md` for anything it added; treat any module of its without a receipt as an ungated draft.
  HANDOFF.md's lane sections were not finalised. No consolidated end-of-round gate was run.
- 05:11 Round released again by the user ("continue"); both lanes resumed with their context. Fable B's
  ledger shows gates 7 and 8 passed before the stop (`1795775517562288460-931660`,
  `1795775689371914965-932255`): K1 → K2 → `FreshApplicationTotal`, and the installed reduction from K1, K2.
- 05:14 Sixth root target frozen and proved: `ActualCalibrationLevelsTargets`
  (sha256 `eb1d0d69f790ebcd4e7d60b7d3336f4227242b804a850cfaecfdadb49a511bda`),
  `ActualCalibrationLevelsProof` **PASS** on the first gate, receipt `1795778069541429314-942177`, standard
  axioms: `exact_DiagonalUnfolding` (Δ'_{l+2} = fix of the level diagonal at Γ_0, every l),
  `exact_CalibrationStep` (one level from `LevelFactsAt l` and `PsiTowerLevelAt l`),
  `exact_AllFromLevels` (`AllTowerCalibration` from those two inputs at every l ≥ 1; n = 0, 1, 2 by the
  existing theorems). Caveat recorded in the targets header: for l ≥ 2 nobody has checked that the per-level
  inputs are true as stated; the implication is what is proved.
- 05:15 **Fable A: calibration at n = 3 is a theorem.** From its ledger, checked against the receipts by script
  (every module row rc 0, no `sorryAx` in any log, standard axioms): gate 2 `1795777920173523546-941350`
  (norm layer; `exact_LevelFacts`), gate 3 `1795777928703118203-941400` (`upperStep`, `lowerStep`),
  gate 4 `1795777954162083312-941567` (**`psiPowerLevel : PsiPowerLevel`**, the frozen T4, unchanged),
  gate 5 `1795777959277796293-941615` (**`calibrationThree : CalibrationThree`**, the frozen T5, through
  root's `exact_ThreeFromPower`). Calibration instances n = 0, 1, 2, 3 are now theorems.
- 05:16 Wrote `root/P16-REALIZATION-WORDING-PROPOSAL.md`: the one-sentence manuscript correction that would let `lem:realization` be adopted on the checked backward closure. Owner decision; not applied.
- 05:17 Fable B returned (second turn). Gated: `exact_FreshApplicationFromLeast` (K1 → K2 →
  `FreshApplicationTotal`), `exact_InstalledAccessibilityFromLeast`, and
  `exact_LiteralWindowSelection` + `exact_BetaJoinedRulesOnLiteralWindow` (receipt
  `1795778131763821298-942489`): one window per closed K carrying the joined beta rules and both reductions —
  the window on which `TypedCarrierComputability` is to be proved. On it, `lem:arithmetic-accessibility`
  rests on K1 (`FreshAddressCarrier`), K2 (`FreshSeedLeast`) and `TypedCarrierComputability`.
  Blocker, with the witnesses named (`fableB/SEED-MEMBER-REPORT.md`): K1/K2 need "the seed occurs in its own
  cover pool", and the cover's syntax program `V` and measure `baseM` are existential witnesses chosen in
  `NumberedWindowInternalFactoredCoverNumericProof.selected` — the round-6 opacity obstacle again. Not
  blocked, only unwritten: `SeedMemberLeast` (pool occurrence ⇒ successor output of `packedLeastOn`),
  frozen in `…SeedMemberLeastTargetsV2`. Resumed on that proof and on scoping an explicit syntax program.
- 14:55 Both lanes had stopped at about 05:20 on an account spend limit (not on their work). On the owner's "please continue" both were resumed. On disk at that point — Fable A: gate 6 passed (`ActualCalibrationLevelOneProof`, receipt `1795778199692925204-942837`: `LevelFactsAt 1` and `PsiTowerLevelAt 1` for every solution, so root's per-level interface is instantiated at level 1); `LEVEL-L-NOTE.md` announced in its ledger but not on disk. Fable B: three modules of the selection restatement written without receipt (`…WindowWithLeastTargetsV2`, `…WindowWithLeastProofV2`, `…LambdaRulesWithLeastV2`).
- 14:56 Seventh root target frozen and proved: `ActualCalibrationLevelsLimitTargets` (sha256 `d57f84723c6e04ff5f51a44d7c38b4904c5bfc0f7ab98d970b8f210b3cdc6068`), `ActualCalibrationLevelsLimitProof.exact_LevelDiagonalLimit` **PASS** first gate, receipt `1795812933152467877-1085623`, standard axioms: the third conjunct of `LevelFactsAt l` holds at every level (limit clause of the orbit read through the spine). Per level, the function side now needs only: diagonal strictly increasing; Γ_0 below the diagonal from 1 on.
- 14:57 Fable B returned (third turn). Gated before the stop, receipt `1795778392935152296-943657` (checked: no
  `sorryAx`): `exact_LambdaWindowWithLeast`, `exact_LiteralWindowWithLeast` — the selected window now also
  exports `A.least = memoFilteredLeast C (joinedBiAuxBase …) s` and `MemoSelectedReports`, so a law about
  the least program can be instantiated there. `fableB/EXPLICIT-COVER-SCOPE.md` corrects its earlier
  report: the cover's generator is an explicit named program; the syntax and measure are visible memo
  wrappers around opaque Primrec-realized leaves (`V`, `baseM`; window leaves `base`, `T`). Consequence:
  **K2 (application seed) needs no explicit leaf program** — it needs `SeedMemberLeast` plus two
  auxiliary-node introduction laws; **K1 (variable payload) is the real opacity case**, unless the wrappers
  decide variable nodes before calling the leaf (not yet checked). `SeedMemberLeast` not started: B stopped
  because its session had grown long. A fresh Fable session (B2) takes `SeedMemberLeast` and K2 with a
  narrow brief; B's session is retired.
- 14:59 Settled the K1 question by reading the wrappers (`root/K1-VARIABLE-NODE-FINDING.md`): `auxSyntaxUpdate` and `measureUpdate` intercept only tag-six auxiliary rows and call the opaque leaf on every other row, so K1 is not derivable for the installed programs; smallest repair = a visible front test for variable nodes on the four leaves, with all-input calibration preserved. K2 unaffected.
- 15:20 **Fable B2 returned: K2 is a theorem; accessibility now rests on K1 and `TypedCarrierComputability`.**
  Receipts checked by script (all rows rc 0, no `sorryAx`): `exact_SeedMemberLeast`
  (`1795813243959391076-1087336`; a corollary of the accepted `exact_OpenLeastOnFromSeed`);
  `exact_SeedLeastOnJoinedWindow` (`1795813854108336678-1090735`); `exact_LiteralWindowWithSeedLeast`
  (`1795813935784752720-1091243`): a selection that additionally exports the rank/type guards, on whose
  window `FreshSeedLeast A c` holds for every c — this window supersedes the one of
  `exact_LiteralWindowWithLeast`; the syntax-leaf front test `variableFrontSyntax TV V` with
  `TermSyntaxCalibrated` preserved and its open law (`1795814305566409834-1093361`). K1 plan and what
  already exists in the legacy tree: `fableB2/K1-OBLIGATIONS-NOTE.md`. Resumed on K1.
- 15:22 **Fable A returned: calibration at n = 4 is a theorem.** Receipts checked by script (all rows rc 0, no
  `sorryAx`): level-independent step calculus — `stepBase`, `stepDiagonal` (`1795813154779391068-1086911`),
  `stepSuccessor` (`1795813329715669451-1087857`), `stepLimit`, `stepB0Orbit`
  (`1795813662649156533-1089665`); level 2 — `levelTwoGood` (`1795814001440580672-1091742`),
  `levelTwoWeight` (`1795814259105500337-1093087`), `levelFactsAt_two`, `psiTowerLevelAt_two` and
  **`calibrationAt_four : ∀ A, CalibrationAt A 4`** through root's `exact_CalibrationStep`
  (`1795814433033321726-1094148`). So root's per-level statements are true and proved at l = 1 and l = 2;
  calibration instances n = 0 … 4 are theorems. Open: l ≥ 3, i.e. the uniform induction over the type level;
  A's plan for it is at the end of its ledger and in `fableA/LEVEL-L-NOTE.md`. A's session retired for
  length; a fresh session (A2) takes the uniform induction.
- 19:51 (after another account-limit pause; user said to continue) **Fable B2 returned: K1 is a theorem;
  accessibility now rests on `TypedCarrierComputability` alone.** Receipts checked by script (all rows rc 0,
  no `sorryAx`): domain closure (`1795814537907221097-1094660`); window-leaf front test and payload facts
  (`1795814936169268139-1096771`); packet, rules and window re-selected at the three front-tested leaves, K2
  re-closed there (`1795815242127512412-1098323`); named-leaf memo laws (`1795815595272564203-1100281`);
  `exact_FreshCarrierOnFrontWindow` (K1) and `exact_FrontLiteralWindowTyping` (`1795815925311427086-1102198`):
  for every closed K one installed window on which `CarrierTypingCases` holds outright and
  `TypedCarrierComputability A c → AllTerms A c`. Caveat from the lane: `FrontPacketV2` is generated from the
  coordinator's uncommitted `NumberedWindowInternalLiteralLambdaJoinedMemoPacketProof`; if that file
  changes it must be regenerated. B2's session retired for length; a fresh session (B3) takes
  `TypedCarrierComputability` on that window.
- 19:51 Fable A2 had stopped on the account limit at about 15:50. On disk: `orbitGood`, `towerGood` gated
  (`1795815845408612238-1101794`): the function side ("good") holds for every `B_m` at every type level;
  weight targets and norm/family modules written without receipt. Resumed.
- 20:50 Owner: "pause after the current round of work finishes." No lane will be resumed or started after its
  current turn. Since about 20:14 no gate has compiled: available memory 0.7–1.8 GiB against the checker's
  2048 MiB floor (swap full; an Android emulator of another session 1.7 GiB, two VMs, a browser, other
  sessions). The floor was not lowered. Both lanes told to let their current gate call run to its deadline
  and then hand back with every module without a receipt marked ungated. Fable B3 finding recorded: the
  frozen `ApplicationEdgeMatching` (`matchEdge`) has no carrier premise on the edge's source and is not
  derivable as stated on this window (details in `fableB3/LEDGER.md`); the assembly no longer uses it.
- 21:15 Fable A2 returned and is stopped. Gated (receipts checked: rows rc 0, no `sorryAx`): `familyDiagonal`
  (`1795815470684857486-1099377`), `orbitGood`, `towerGood` (`1795815845408612238-1101794`), `familyLifting`
  and the base families (`1795816095108793665-1103069`) — the function side and the norm side of the uniform
  induction at every type level. **Never compiled** (memory floor closed for both of its last gate calls):
  `ActualCalibrationUniformWeightProof` (`orbitWeight`, `towerWeight`), `ActualCalibrationUniformLevelProof`
  (`allLevels`), `ActualCalibrationAllProof` (`allTowerCalibration`, `calibrationAt_five`) — about 640 lines.
  `AllTowerCalibration` is therefore NOT a theorem; it is three uncompiled modules away, with no known
  mathematical blocker. Gate command and known elaboration traps: `fableA2/LEDGER.md` Entry 6.
- 21:32 Fable B3 returned and is stopped. **Nothing of B3 is compiled**: both of its gate calls timed out on
  the memory floor. On disk, all ungated: `fableB3/TYPED-COMPUTABILITY-MAP.md` (status map of
  `TypedCarrierComputability` on the front window, row by row), and four Targets + Proof pairs
  (`…TypedRows…V2`, `…GeneralSeedLeast…V2`, `…ApplicationResult…V2`, `…FrontRows…V2`); gate order in the map
  §3.2. Its reading (not compiled): the neutral lemma, bottoms, free variables, application inversion,
  computability ⇒ I and the applied-lambda rule exist and need only instantiation at the window; bound
  variables, lambda step inversion, substitution/step commutation, constructor step exhaustion and the
  carrier shape split are blocked on opaque witnesses (`leaves`, `other`, `seed`, `H`, `base₀`, `V₀`), and
  front tests cannot give the two that need the rules' content; the structural induction under substitution
  has no internal statement yet. Finding: frozen `ApplicationEdgeMatching` is not derivable as stated
  (no carrier premise on the edge's source); nothing downstream consumes it.
- 21:32 **Round paused on the owner's instruction.** All lanes stopped; no gate waiting from this round. No
  consolidated end-of-round gate was run (memory floor still closed: about 0.6 GiB available, swap full).
  Every gated result has its own receipt; the ungated modules are listed in HANDOFF.md. No Git operation in
  the whole round. No `.local-run-policy.json` exists in this worktree and none was created.
- 23:05 (after the pause; owner: "set up a method to run lean on the Thinkpad") `verification/remote-thinkpad/`
  (`tp.sh`, `README.md`): the repository's own `scripts/check.py`, same flags, run on the ThinkPad `t14` over
  a mirror of the same absolute paths (toolchain, package objects, sources, cache, receipts), results pulled
  back. Verified three ways: a cached root is 1,573 cache hits there; three never-compiled modules compile
  there; the local checker then accepts those objects as 2,271 cache hits (receipt
  `1795842191159139612-1260377`).
- 23:05 **The set-up test compiled Fable A2's three pending modules, first attempt: `AllTowerCalibration` is
  a theorem.** Receipt `1795842164430545753-2237658` (compiled on the ThinkPad; all rows rc 0, no `sorryAx`,
  standard axioms): `orbitWeight`, `towerWeight`, `allLevels`, **`allTowerCalibration :
  Paper16RemainingOrdinalTargets.AllTowerCalibration`**, `calibrationAt_five`. Sources are byte-identical to
  A2's hand-back (sha256 as in `fableA2/LEDGER.md` Entry 6). Evidence
  `evidence/P16-ALL-TOWER-CALIBRATION-EVIDENCE.json`. No proof work was done after the pause; the round stays
  paused. Not done: composing this with `exact_HeightFromInputs` / `exact_PrintedFromInputs` to drop the
  calibration input from the ordinal assembly (two or three lines each; first thing for a resumed round).
  Fable B3's eight modules remain uncompiled.
