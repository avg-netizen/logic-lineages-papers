# Fable B ledger — internal accessibility lane, 27 November 2026 (clock times UTC−6, read from `date`; untimed entries are in order)

Append-only. Module names below carry the prefix `LogicLineages.NativeModule.PersistentMarking.`;
receipts are in `build-reports/<id>.json` under the package root.

- (start) Read BRIEF, TARGETS.md (internal accessibility), the 26 November handoffs, round-6
  ACCESSIBILITY-PLAN / OPEN-TERM-ARITHMETIC-NOTE, and the V2 milestone modules. Plan in `PLAN.md`.
- (before first gate) Target chosen (already frozen, no new Targets module needed):
  `Paper16AccessibilityMilestoneTargetsV2.FinishMultisets`
  (`Paper16AccessibilityMilestoneTargetsV2.lean`, sha256
  `23f666331005a2037ed6e1ca8ba1ea16d5da5665ed207b26540b6d25ca2b41de`).
  New proof module `Paper16AccessibilityMilestoneFinishMultisetsV2`
  (sha256 `2d60871966644eb8c513d59f8192b8c32c576f3a876e7227c102e4943a64b108`).
- 04:02 **GATE PASS**, receipt `1795773714932362718-921018` (1,637 rows; first attempt; log
  `gate-1-finish-multisets.log`). Theorems: `exact_SingletonFromUnionClosure`,
  `exact_MembersFromUnionClosure`, `exact_UnionClosureFromCertified`, `exact_FinishMultisets`.
  Axioms: `propext`, `Quot.sound` (first two); `propext`, `Classical.choice`, `Quot.sound` (last two).
  Evidence: `FINISH-MULTISETS-EVIDENCE.json`.
  Note: `MultisetGeneration.unionCarrier` is not consumed by the proof (the certified union step
  returns J-membership directly); the round-6 `MultisetSplit` premise is not used at all.
- (after gate 1) `PLAN.md` written: reading results, agenda A–C, what is not attempted.
- Targets frozen: `Paper16AccessibilityMilestoneArrowTypingTargetsV2` (definitions only; source map
  `ARROW-TYPING-SOURCE-MAP.md`). Depends on the gated `Paper16AccessibilityMilestoneTargetsV2` and
  three definition/target modules. Proof module `Paper16AccessibilityMilestoneArrowTypingProofV2`
  imports `Paper16AccessibilityMilestoneArrowTypedIntroductionV2`, which root gated today
  (receipt `1795773831011891982-921759`, returncode 0) — no ungated dependency.
- 04:11 **GATE PASS**, receipt `1795774234561241622-924414` (1,691 rows; first attempt; log
  `gate-2-arrow-typing.log`): `Paper16AccessibilityMilestoneArrowTypingTargetsV2`
  (sha256 `dfd27747d4e736c0e3c310f8bc7b3d6a1a750cbea04a62325de1890070569037`, frozen) and
  `Paper16AccessibilityMilestoneArrowTypingProofV2`
  (sha256 `0c34b154302378d54e3f0f8133de573c59a521c337478c2150be3866b2507208`): theorems
  `exact_StoredTypingFromReports`, `exact_TypingCasesFromReports`; axioms `propext`,
  `Classical.choice`, `Quot.sound`.
- 04:14 Gate FAIL, receipt `1795774440893838995-925628` (log `gate-3-arrow-install.log`):
  `Paper16AccessibilityMilestoneArrowTypingInstallTargetsV2` **compiled**
  (sha256 `465712db58cb67def3e277bec4a39bec5a1413c88c890124e1e22fbbedfc26c0`, frozen from here);
  `…ArrowTypingInstallProofV2` failed with one error: a `Nonempty` was eliminated inside a
  `have` whose goal was a `Derivation` (Type-valued). Failed source kept at
  `../drafts/fableB/Paper16AccessibilityMilestoneArrowTypingInstallProofV2.attempt1.lean.txt`.
  Repair: the elimination moved to the Prop-valued goal.
- 04:14 Root ledger: `…InstalledLambdaWindowV2` is blocked by an unresolved identifier in the
  coordinator's uncommitted `NumberedWindowInternalLiteralJoinedBetaOutcomeProof`. Consequence for
  this lane: the selection theorem cannot be gated today. The assembly was therefore split out into
  a statement whose hypotheses are the facts the joined rules provide
  (`Paper16AccessibilityMilestoneArrowTypingAssemblyTargetsV2`, sha256
  `2891fda3ce1bba9cb808cf26ccfea9f7781383dd99ed9256fe5be4663d9067eb`, frozen), so that everything
  except the final ten-line instantiation is gated. First selection draft kept at
  `../drafts/fableB/Paper16AccessibilityMilestoneArrowTypingSelectionProofV2.attempt1.lean.txt`.
- 04:18 **GATE PASS**, receipt `1795774692720129882-927148` (log `gate-4-install-assembly.log`):
  `…ArrowTypingInstallProofV2` (sha256
  `31752c63434e89e56784c4b11c989753caeec6753750079c7651e3a7a06f765f`,
  `exact_StackedLiteralProbeReports`), `…ArrowTypingAssemblyTargetsV2`, and
  `…ArrowTypingAssemblyProofV2` (sha256
  `68a8cd09cb0065b95847a0479c997e1e943871b98f92392a73a68a7e795dd868`,
  `exact_WindowReductionFromJoinedFacts`). Axioms `propext`, `Classical.choice`, `Quot.sound`.
- DRAFT, not gated: `…ArrowTypingSelectionProofV2` (sha256
  `ae2b92e51d1745bd2bbd926042e249b6fd2ba50500127dc8fc263a006731f9c8`),
  `exact_InstalledAccessibilityReduction : InstalledAccessibilityReduction`. Depends on the ungated
  `…InstalledLambdaWindowV2` (blocked as above).
- `FRESH-APPLICATION-REPORT.md` written: the open obligation `FreshApplicationTotal`, the two
  least-program totality facts it reduces to (K1, K2) with supplier theorem names, why the guard
  device does not apply, and the relation to `matchEdge`.
- 04:18 Root ledger: root applied the verified one-token repair to the coordinator's
  `LogicLineages/PersistentMarking/NumberedWindowInternalLiteralJoinedBetaOutcomeProof.lean`
  (`open … (eqn eqnRelabel …)`), which unblocks `…InstalledLambdaWindowV2`. This lane did not edit
  that file.
- 04:20 **GATE PASS**, receipt `1795774776803253954-927590` (3,961 rows; first attempt; log
  `gate-5-selection.log`): `Paper16AccessibilityMilestoneArrowTypingSelectionProofV2`
  (sha256 `ae2b92e51d1745bd2bbd926042e249b6fd2ba50500127dc8fc263a006731f9c8`),
  `exact_InstalledAccessibilityReduction : InstalledAccessibilityReduction`; axioms `propext`,
  `Classical.choice`, `Quot.sound`. Its closure contains the coordinator's uncommitted modules,
  including `…InstalledLambdaWindowV2` and the file root repaired; the receipt pins the hashes
  actually compiled. Evidence: `ARROW-TYPING-EVIDENCE.json`, `SELECTION-EVIDENCE.json`.
- 04:23 Targets frozen: `Paper16AccessibilityMilestoneArrowTypingGroundTargetsV2`
  (sha256 `ef3a3740553bcbf52cc6e33325b39e4b09319ce5b1978b19b655316161d39865`,
  `GroundUniverseReduction`). **GATE PASS**, receipt `1795774915562672368-928420` (first attempt; log
  `gate-6-ground.log`): that module and `Paper16AccessibilityMilestoneArrowTypingGroundProofV2`
  (sha256 `1ef5d7b15e42ea8660f783ebe09170691c7a54f2b7b5df9179b1a791a7f856e9`),
  `exact_GroundUniverseReduction`; axioms `propext`, `Classical.choice`, `Quot.sound`.
- Not attempted in Lean (recipe in `FRESH-APPLICATION-REPORT.md`): reducing `FreshApplicationTotal`
  to the two least-program facts K1 (carrier of the packed free address) and K2 (successor output
  on the application seed) through `exact_OpenParsedFresh`,
  `exact_OriginalLiteralAddressReport`, `exact_OpenAddressArrowCoordinates` and
  `exact_OpenLiteralApplicationFromReportedLeast`. It is finite-shape work (one six-variable block
  elimination, one existential introduction, renaming lemmas for `typedResultAt`); stopped before
  it to leave the records complete.

## State and next (end of round)

Gated theorems (all first-attempt passes except one repaired module; standard axioms only):

| Theorem | Module (`…Paper16AccessibilityMilestone…`) | Receipt |
| --- | --- | --- |
| `exact_FinishMultisets` (frozen `TargetsV2.FinishMultisets`, every window/context/programs) | `FinishMultisetsV2` | `1795773714932362718-921018` |
| `exact_StoredTypingFromReports`, `exact_TypingCasesFromReports` | `ArrowTypingProofV2` | `1795774234561241622-924414` |
| `exact_StackedLiteralProbeReports` | `ArrowTypingInstallProofV2` | `1795774692720129882-927148` |
| `exact_WindowReductionFromJoinedFacts` | `ArrowTypingAssemblyProofV2` | `1795774692720129882-927148` |
| `exact_InstalledAccessibilityReduction` | `ArrowTypingSelectionProofV2` | `1795774776803253954-927590` |
| `exact_GroundUniverseReduction` | `ArrowTypingGroundProofV2` | `1795774915562672368-928420` |

Frozen Targets modules of this lane: `ArrowTypingTargetsV2`, `ArrowTypingInstallTargetsV2`,
`ArrowTypingAssemblyTargetsV2`, `ArrowTypingGroundTargetsV2` (hashes above and in
`ARROW-TYPING-SOURCE-MAP.md`).

What this establishes for `lem:arithmetic-accessibility`. For every closed source universe `K`
there is one installed window `B` over `sourceWindow K` (the joined lambda window with literal
probe leaves) such that, for every context numeral `c`,
`FreshApplicationTotal B c → CarrierTypingCases B c` and
`CarrierTypingCases B c → TypedCarrierComputability B c → AllTerms B c`.
So `AllTerms` — and with it `InstalledArithmeticAccessibility` on that selection — is reduced to
two statements on one window: `FreshApplicationTotal` and `TypedCarrierComputability`. The
`ApplicationArithmetic` premise of `exact_CloseAllTerms` is no longer needed on this window; its
`matchEdge` field stays unproved and unused. On ground-only universes the type split is
unconditional. Separately, the multiset checkpoint `FinishMultisets` is a theorem.

Nothing in the comparison register changes: the two remaining premises are open, so
`lem:arithmetic-accessibility` stays pending.

Dependencies on work that is not this lane's: the selection and ground theorems compile against
the Codex coordinator's uncommitted modules (in particular
`Paper16AccessibilityMilestoneInstalledLambdaWindowV2`) and against
`NumberedWindowInternalLiteralJoinedBetaOutcomeProof` as repaired by root on 27 November. The
receipts pin the source hashes that were compiled. If the coordinator changes those files, rerun
gate 5 and gate 6.

Next, in order:
1. `FreshApplicationTotal` on the selected window: first the finite-shape reduction to K1/K2,
   then the internal totality of `packedLeastOn` on a seed that lies in its own cover pool
   (`FRESH-APPLICATION-REPORT.md`, last section). This is the only missing piece of the type split.
2. `TypedCarrierComputability` on the same window `literalProbeWindow A`: the beta/lambda lanes'
   rules are stated on `A`'s presentation and application guard, which `literalProbeWindow` keeps;
   the fields that mention `chosenH`/`chosenA` are rebuilt as in
   `exact_WindowReductionFromJoinedFacts`.
3. The premises of `FinishMultisets` (`CertifiedMultisetUnion`, `MultisetGeneration`) when the
   constructor induction needs J.

## Continuation (root's follow-up message: items 1 and 2)

- Targets frozen: `Paper16AccessibilityMilestoneFreshApplicationTargetsV2`
  (sha256 below at first gate): `leastSelectedAt`, K1 `FreshAddressCarrier`, K2 `FreshSeedLeast`,
  `FreshApplicationFromLeast`, `InstalledAccessibilityFromLeast`. K2 is stated for the fresh probe
  only (the case `ValidWindow`'s numerical totality covers), not for arbitrary argument addresses.
- 04:31 **GATE PASS**, receipt `1795775517562288460-931660` (first attempt; log
  `gate-7-fresh-application.log`): `Paper16AccessibilityMilestoneFreshApplicationTargetsV2`
  (sha256 `d9a8c926d90d427b254c77c230fbcb0e05784a996656f5922a112e0e2a7a60fe`, frozen) and
  `…FreshApplicationProofV2` (sha256
  `4ae11367dd2de11822161fe56e6c89c558ead25fc20c0cb84747551816a2d678`):
  `exact_FreshApplicationFromLeast : FreshApplicationFromLeast`
  (K1 → K2 → `FreshApplicationTotal` on any window with the installed guarded core). Axioms
  `propext`, `Classical.choice`, `Quot.sound`.
- 04:34 **GATE PASS**, receipt `1795775689371914965-932255` (first attempt; log
  `gate-8-fresh-selection.log`): `…FreshApplicationSelectionProofV2` (sha256
  `f17f5ce26a85179ed20ef87d3d36eb2f259de5213ea90053b0aba3ed718e2dae`):
  `exact_InstalledAccessibilityFromLeast : InstalledAccessibilityFromLeast` — on
  `literalProbeWindow A` of the joined lambda window, `K1 → K2 → CarrierTypingCases` and
  `CarrierTypingCases → TypedCarrierComputability → AllTerms`. Same axioms.
- (after the pause) Check requested by root: no file was started after gate 8. Every module this
  lane has written has a passing receipt; there is no ungated draft. Between gate 8 and the pause
  only definitions of the least program's components were read (item 2).
- 05:14 Gate FAIL, receipt `1795778103135904967-942357` (log `gate-9-literal-window.log`). Two
  Targets modules **compiled** and are frozen from here:
  `Paper16AccessibilityMilestoneSeedMemberLeastTargetsV2` (sha256
  `4e4eb17c5f9ea79a4750f81651093ab3087b80ae6b4096f4c0465a9a8b21ff2b`; `SeedMemberLeast`, statement
  only, **not proved**) and `…LiteralWindowTargetsV2` (sha256
  `11f9619166fba4084a264eb2513d22c58a7efcc4280d4437bd46d02e5808663c`; `LiteralWindowSelection`).
  `…LiteralWindowProofV2` failed on a missing `open`; failed source kept in `../drafts/fableB/`.
- 05:15 **GATE PASS**, receipt `1795778131763821298-942489` (log `gate-10-literal-window.log`):
  `…LiteralWindowProofV2` (sha256
  `f5163846889bec45aedd92d74f6b09128783618270f1df7ab35543c437d0a926`):
  `exact_BetaJoinedRulesOnLiteralWindow`, `exact_LiteralWindowSelection`. Axioms `propext`,
  `Classical.choice`, `Quot.sound`. Evidence for gates 7–10: `CONTINUATION-EVIDENCE.json`.
- Item 2 result: blocked, reason recorded in `SEED-MEMBER-REPORT.md`. The membership half
  (`SeedMemberLeast`) concerns visible code and is inductive, not written. The pool-occurrence half
  fails on opaque witnesses: the cover's syntax program `V` and measure `baseM`
  (`exact_SelectedFactoredCover`, from `termProgram` / `measureExists` / `grammarExists`), and for
  K1 also the window leaves `base`, `T` (`exact_WindowPrimitiveLeaves`). In addition the lambda
  window theorem does not export `A.least`'s code or `MemoSelectedReports`.
- `TypedCarrierComputability` on the literal window: stated as the last conjunct of the gated
  `LiteralWindowSelection`, on the same window as the joined rules. Transfer of the beta/lambda
  rules to `literalProbeWindow A` (theorem `exact_BetaJoinedRulesOnLiteralWindow`): unchanged —
  `inversion`, `arithmetic`, `forward`, `pullback`, `applicationOutput`, `betaCases`, and the
  window equations (`A.raw`, `A.scalar`, `A.application`, guard) and instance fits; rebuilt —
  `fresh` (`FreshVariablesComputable`) and `typedComputableToMember`, the two fields that mention
  `chosenH`/`chosenA`. Consumers that take `CarrierTypingCases A c` as a hypothesis
  (`…BetaAddressProof`, `…BetaLambdaConsumerProof`) are stated for an arbitrary window and apply to
  the literal window as they are; they were not re-run here.

## State and next (after the continuation)

New gated theorems: `exact_FreshApplicationFromLeast` (`1795775517562288460-931660`),
`exact_InstalledAccessibilityFromLeast` (`1795775689371914965-932255`),
`exact_BetaJoinedRulesOnLiteralWindow` and `exact_LiteralWindowSelection`
(`1795778131763821298-942489`). No ungated draft. One frozen statement without proof:
`SeedMemberLeast`.

`lem:arithmetic-accessibility` on the selected window now rests on K1 `FreshAddressCarrier`,
K2 `FreshSeedLeast` and `TypedCarrierComputability`; the window carrying all joined rules and both
reductions is the one of `LiteralWindowSelection`.

Next: (1) decide the visible-code route for the cover (explicit `V`, measure and generator, or a
`V`-guarded cover) — K1/K2 cannot be closed for the present witnesses; (2) prove `SeedMemberLeast`
(three nested inductions on visible code); (3) a lambda-window selection that exports
`A.least = memoFilteredLeast C Base s` and `MemoSelectedReports`; (4) `TypedCarrierComputability`
on the window of `LiteralWindowSelection`, using its `BetaJoinedRulesAt`.

## Second continuation (root's order: A `SeedMemberLeast`, B selection restatement, C scope report)

- 05:19 Item B written first because it is a restatement: three modules,
  `Paper16AccessibilityMilestoneLambdaRulesWithLeastV2`,
  `…WindowWithLeastTargetsV2`, `…WindowWithLeastProofV2`. They were on disk as **ungated drafts**
  with no ledger entry when the session was interrupted by an account limit (root's note). The
  gate launched in the same step had in fact finished; entry below.
- **GATE PASS**, receipt `1795778392935152296-943657` (first attempt; log
  `gate-11-with-least.log`; the three hashes are in `WITH-LEAST-EVIDENCE.json`):
  - `…LambdaRulesWithLeastV2`: `exact_ConcreteLambdaJoinedRulesWithLeastAt` — the coordinator's
    `exact_ConcreteLambdaJoinedRulesAt` (statement and proof text taken from
    `NumberedWindowInternalLiteralConcreteLambdaJoinedRulesProof`, generated by script, original
    untouched) with one more conjunct `MemoSelectedReports C s Base`.
  - `…WindowWithLeastTargetsV2` (frozen): `LambdaWindowWithLeast`, `LiteralWindowWithLeast`.
  - `…WindowWithLeastProofV2`: `exact_LambdaWindowWithLeast`, `exact_LiteralWindowWithLeast`. Both
    export, for the selected window, the exchange program `X`,
    `A.least = memoFilteredLeast C (joinedBiAuxBase s X base Tg V A.typeGuard baseM) s` and
    `MemoSelectedReports C s (joinedBiAuxBase …)`; the second is on the window with literal probe
    leaves and carries the joined rules and both reductions. Axioms `propext`,
    `Classical.choice`, `Quot.sound`.
- Item C: `EXPLICIT-COVER-SCOPE.md` written. It **corrects** `SEED-MEMBER-REPORT.md`: the
  installed cover's generator is the named program `selectedGrammarOption`, and the syntax and
  measure arguments are visible memo wrappers (`unitAuxSyntax`, `chosenMeasure`); only their leaf
  programs `V`, `baseM` (and the window leaves `base`, `T`) are Primrec-realization witnesses. So
  K2 (application seed, an auxiliary node) needs no explicit leaf program; K1 (variable payload, a
  leaf) does, unless the wrappers decide variable nodes before calling the leaf (not opened).
- Item A (`SeedMemberLeast`): **not started in Lean.** No layer written, no draft on disk.

## State and next (after the second continuation)

Gated this continuation: `exact_ConcreteLambdaJoinedRulesWithLeastAt`,
`exact_LambdaWindowWithLeast`, `exact_LiteralWindowWithLeast` (receipt
`1795778392935152296-943657`). No ungated draft. Frozen without proof: `SeedMemberLeast`.

Next: (1) `SeedMemberLeast` in layers — (L1) `scratchMinimum` returns a successor on a list with an
occurrence (list induction; `minimumStep` is `branch (π1) offerHead (branch preferHead (π1) offerHead)`);
(L2) `scan E` accepts a candidate that occurs in the seen list (list induction; equality clause of
`scanStep`); (L3) `pass E` keeps a pool entry that occurs in the seen list (list induction over the
pool, using L2, `consElimination`, `headMember`/`tailMember`); (L4) every round lists the seed
(natural induction over the fuel, `roundBase`/`roundStep` are `pass`); (L5) assembly through
`members`, `minimumAtMembersOn`, `successorBranchIntro`. (2) Check whether `unitAuxSyntax` /
`chosenMeasure` decide variable nodes before the leaf call; that settles whether K1 needs an
explicit program. (3) The two auxiliary-node introduction laws for K2.
