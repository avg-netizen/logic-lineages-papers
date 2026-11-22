# Opus A ledger — 2026-11-22 (times UTC−6)

- 15:30 Read BRIEF.md, root ledger, #1386 Targets/Proof, #1379 cross-cover, #825 packed domain, #832
  covered installation. Prefixes `…PairedCommonLeast` / `…PairedSharedMeasure` unused (grep).
- Finding: #832 got existence from `exact_CoveredWindowReport` (specific to `coveredWindow`). The
  thin analogue already exists and is accepted: #1338 `exact_OpenCoverThinMatchingWindowReport`
  (`windowAt (thinMatchingWindow C s baseW V) ctx ty raw → occursInCover ⊓ hasLeast C X W …`,
  generic in C, baseW, V, X). It reads the context parse off the window's own `thinContextPresent`
  conjunct, so no context-parse hypothesis is needed and the memberA/scratchA route through #825
  directly is unnecessary.
- 15:35 **Frozen** `LogicLineages/PersistentMarking/NumberedWindowInternalCoverCombinedRestrictedPairedCommonLeastTargets.lean`
  sha256 `fa6faafe2d2a585f08c7b8cf1146b888a98d6198caf755bc86e2b48e877f9a4b`
  (`ExactOpenCoverCombinedRestrictedPairedCommonLeast`). Source map `opusA/PAIRED-COMMON-LEAST-SOURCE-MAP.md`.
- 15:39 **Gate PASS** `LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPairedCommonLeastProof`
  (also compiled the frozen Targets and the uncached accepted `…WrapperReportProof`), receipt
  `1795383502273947273-3141179`; `exact_OpenCoverCombinedRestrictedPairedCommonLeast`
  `[propext, Classical.choice, Quot.sound]`. Proof sha256
  `34b2dfe568839139818fe9c5ce9695e1d52addfa481d7af13a9156f4fd5fb53e`. No added hypothesis.
  Route: #1386 edge both ways → `exact_OpenPackedScalarEdge` windows at a, b → #1338 `hasLeast` at a, b →
  `casesLeast` at a (fresh x) → inside, `casesLeast` at b (fresh y), #818 gives `eqn x y`,
  `outputTransport` + `congSuc (symm …)` moves the b-least to x. Evidence `opusA/PAIRED-COMMON-LEAST-EVIDENCE.json`.
- 15:40 Task 2 survey. #858 (`exact_OpenAuxMeasureEquality`) is stated for `selectedMeasure (measureUpdate base combine)`,
  NOT for the combined programs' measure: `P.R` unfolds (all abbrevs down to `refinedPrograms`) to
  `sharedMeasureUpdate (fittedMeasureBase …)`, so `selectedMeasure P.R` is `sharedMeasure N` (lambda-dispatching
  update, `NumberedWindowInternalCoverSharedRecursionTargets`). #858 therefore does not apply literally. The shared
  analogue is provable from accepted #1076 `exact_OpenCoverSharedAuxMeasureParent` (decomposition of a tag-six
  parent measure under `sharedMeasure M` into fn/arg selected measures + `chosenCombine p ![mf,ma]`) plus
  `valueUnique`. Existence of the application measures needs no hypothesis: `programCases` (program totality in
  the calculus) supplies them.
- Finding (negative, task 2b): the shared function measure does NOT follow from the two opposite parent edges.
  `directedX base P.V = selected (step base V)` with `base : Program 2` universally quantified; an edge f→g is
  `base(f,g)` or the memo branch for auxiliary children, plus the two windows (syntax + own cover at each seed's
  own measure). Nothing compares the measures of f and g (take `base` constantly accepting: in the standard
  model the edges hold for f, g of different measure). So a measure hypothesis must remain; the weakest one the
  suppliers support is at the function level: `unary (selectedMeasure P.R) m f`, `… m g`.
- 15:45 **Frozen** `LogicLineages/PersistentMarking/NumberedWindowInternalCoverCombinedRestrictedPairedSharedMeasureTargets.lean`
  sha256 `c01b0d9896e131e037735cb11ade6e5e22669f483f745fe5e0286e56d3c9e7d9` (Targets alone compiled, receipt
  `1795383944437755657-3145798`). Four statements: `ExactOpenSharedAuxMeasureEquality` (generic M),
  `…PairedSharedMeasureParent`, `…PairedSharedMeasureEdge`, `…PairedSharedMeasureCommonLeast`.
  Source map `opusA/PAIRED-SHARED-MEASURE-SOURCE-MAP.md`.
- 15:47 **Gate PASS** `…PairedSharedMeasureEqualityProof` (sha256 `f676daa1…cf47e6`), receipt
  `1795384092628823605-3146358`: `exact_OpenSharedAuxMeasureEquality`, `exact_OpenCoverCombinedRestrictedPairedSharedMeasureParent`,
  both `[propext, Classical.choice, Quot.sound]`. Route: `programCases` at `arg` gives `ma0`; #1076 decomposes each
  parent measure into `chosenCombine x ![mf,ma]`; `valueUnique` pins `mf = m`, `ma = ma0`; input transport, then
  `valueUnique chosenCombine` gives `x = y`. Parent: `programCases` at `a` gives `p`; `programCases` at `b` gives `q`,
  equality + `outputTransport` move it to `p`. Unifier found `P.R = sharedMeasureUpdate ?N` with no explicit N.
- 15:48 **Gate PASS** `…PairedSharedMeasureProof` (sha256 `cf926d9c…aa1f`), receipt `1795384163800122757-3146619`:
  `exact_OpenCoverCombinedRestrictedPairedSharedMeasureEdge`, `exact_OpenCoverCombinedRestrictedPairedSharedMeasureCommonLeast`,
  both `[propext, Classical.choice, Quot.sound]`. Joint cached gate of both proof modules `1795384188320039425-3146713`.
  Evidence `opusA/PAIRED-SHARED-MEASURE-EVIDENCE.json`.

## State and next (15:50)

Both tasks passed; nothing drafted-but-ungated; no failed routes.
1. `…PairedCommonLeast`: from the #1386 parent hypotheses alone, one fresh `x` with both packed least calls. No
   added hypothesis (the context parse is inside `thinMatchingWindow`; #1338 already packaged #825 for it).
2. `…PairedSharedMeasure{Edge,CommonLeast}`: same with the shared *application* measure replaced by a shared
   *function* measure of f and g. Fully measure-free is not available: the parent edges carry no measure
   information (arbitrary `base`). The two hypothesis forms are not known to be comparable: application ⇒
   function would need `chosenCombine` injective in its first argument (no accepted lemma); function ⇒
   application is what was proved here.
Next candidates for root: (a) if the frontier wants the function measure discharged, it has to come from the
exchange relation itself (e.g. a calibrated `base` that only relates measure-equal heads, or a
`measuredExchange`-style guard: `NumberedWindowInternalMeasuredAuxExchangeTargets.measuredExchange` compares
measurements and looks like the intended device); (b) the handoff's "mutual inclusion of reached pools" route is
not needed for equal minima (#1386) nor for their existence (this lane).

## Task 3 (root message after #1390–#1392): application least along a whole round

- 15:56 Read #835 (RoundLeast Targets/Syntax/Core/Induction/Checks). Prefix `…RoundApplication` unused.
  Design: #835's block binds 7 variables and its premise is context-free (`SameLeastOnEdge`). For the combined
  programs the edge step needs held side facts (guards, argument window), so the main statement takes a
  *relative* premise `ApplicationEdgeStepAt … Γ …` (asked only in renaming-extensions of Γ); the
  context-free `ApplicationEdgeStep` (SameLeastOnEdge style) gives a corollary. The block binds only the two
  varying variables (pool, member); everything else is a fixed parameter. Motive = `unary N μ k ⊓
  leastGraph C X W s ctx ty (auxiliaryTerm dom cod k arg) m`; function-level edge program `E` and
  application-level programs `C X W s`, measure program `N` are independent parameters. Seed motive is an input.
- **Frozen** `LogicLineages/PersistentMarking/NumberedWindowInternalCoverCombinedRestrictedRoundApplicationTargets.lean`
  sha256 `983d7a76af722947fd75492a2e261afe71ba969be45b0aa728155174fbe79da5` (compiled alone, receipt `1795384549289587332-3148056`): `appMotive`, `ApplicationEdgeStep`,
  `ApplicationEdgeStepAt`, `ExactRoundApplicationLeastAt`, `ExactRoundApplicationLeast`.
- 16:0x **Gate PASS** `…RoundApplicationSyntaxProof` (receipt `1795384701261812025-3148639`; matrix/AtCount over two bound
  variables, subst/rename lemmas, `moveMotive` along `eqn w k`, `stepRename`) and `…RoundApplicationProof`
  (receipt `1795384984519409430-3150389`): `exact_RoundApplicationLeastAt`, `exact_RoundApplicationLeast`, both
  `[propext, Classical.choice, Quot.sound]`. #835 core lemmas reused: `exact_ZeroRoundOrigin`,
  `exact_SuccessorRoundOrigin`, `exact_RetainedPredecessor`, `witnessUnfold`/`witnessBinder`, `roundRename`/`roundSubst`.
  Re-derived (motive-dependent, cannot reuse): base/witness/step cores, `AtCount`, `applyAt`, zero/succ rows.
  The retained-equality case transports `auxiliaryTerm … k arg` along `eqn w k` by equality elimination on the
  whole motive (no extra input). The seed motive is an input, as the plain motive's seed least was in #835.
- 16:06 **Frozen** `LogicLineages/PersistentMarking/NumberedWindowInternalCoverCombinedRestrictedRoundApplicationCombinedTargets.lean`
  sha256 `af6fb9e5111f70605bb24500f966015feca0fd2c68958ae70303183de11f97e7` (compiled alone, receipt `1795385191995639041-3151452`): `MeasurePreservingEdge`,
  `ExactCombinedApplicationLeastStep`, `ExactCombinedApplicationEdgeStepAt`, `ExactCombinedRoundApplicationLeast`,
  `ExactMeasuredExchangePreservesMeasure`. Supplier found for the measured half: accepted #862 closure has
  `NumberedWindowInternalMeasuredAuxExchangeCompareProof.compareCases` (accepted compareMeasurements ⇒ common m).
- 16:1x **Gate PASS** `…RoundApplicationCombinedProof` (sha `7b0e4936…f9a4b`… see evidence), receipt
  `1795385307331069225-3151911`: `pairedParentEdges` (guarded paired edge ⇒ D-edge both ways + windows),
  `exact_CombinedApplicationLeastStep` (least half, from a shared measure of w and k; no premise),
  `exact_CombinedApplicationEdgeStepAt` and `exact_CombinedRoundApplicationLeast` (under `MeasurePreservingEdge` only).
  **Gate PASS** `…RoundApplicationMeasuredProof`, receipt `1795385340656034329-3152017`:
  `exact_MeasuredExchangePreservesMeasure` — for `guardedExchange C s (thinPairedExchange (measuredExchange M D))`,
  any C s M D W, measure preservation is a theorem (via #862-closure `compareCases`). All axioms standard.
  Evidence `opusA/ROUND-APPLICATION-COMBINED-EVIDENCE.json`; (a) evidence `opusA/ROUND-APPLICATION-EVIDENCE.json`.
- Measured-exchange answer (proof-level): `measuredExchange M D = conjunction D (compareMeasurements M)` =
  `.composition conditional ![…]`; `directedX base V = .composition (scratchRow …) ![pair,…]` — not of the form
  `directedX base' P.V`. Which accepted results need D = directedX: only the lift #1370
  (`ExactOpenCoverCombinedRestrictedDirectedX`, uses the memo branch) and hence #1377/#1379/#1386/#1390–#1392 as
  stated. Generic in the exchange: #818 (any baseX), #1338 (any X), `guardedOfActualPair` (any D),
  `exact_OpenPackedScalarEdge`. So for the measured exchange the function-level edge unpacks (conjunctionRecover)
  into the D-edge (feeds #1370 unchanged) plus `compareMeasurements` (gives a shared function measure via
  `compareCases`), i.e. exactly the inputs of #1392 — no measure hypothesis left.
- 16:2x **Frozen** `LogicLineages/PersistentMarking/NumberedWindowInternalCoverCombinedRestrictedRoundApplicationRepresentativeTargets.lean`
  sha256 `84ad689b2c5b8f07eefed95b50d5cb89642058072712e98bfc74abaf123027ef` (compiled alone, receipt
  `1795385537101036829-3152762`): `ExactLeastRepresentativeApplication` (generic (c)), `ExactMeasuredToPlainEdge`,
  `ExactMeasuredCombinedApplicationEdgeStepAt`, `ExactMeasuredCombinedRoundApplicationLeast`,
  `ExactCombinedLeastRepresentativeApplication` (unmeasured, under MeasurePreservingEdge),
  `ExactMeasuredCombinedLeastRepresentativeApplication` (measured function least, no premise).
- 16:2x Gate FAIL `…RoundApplicationRepresentativeProof` twice (receipts `1795385590667437564-3152968`,
  `1795385613435124896-3153088`): `rw [unaryRename]` did not see `programGraph … ![f]` as `unary`; draft archived
  `drafts/opusA/RepresentativeProof-v1.*`; fixed with a typed `replace`. **Gate PASS** receipt
  `1795385640581243464-3153208` (`exact_LeastRepresentativeApplication`, sha `de4df8cf…df1a`).
- **Gate PASS** `…RoundApplicationMeasuredCombinedProof` (sha `338ee4f1…957d`), receipt
  `1795385713754905498-3153640`: `exact_MeasuredToPlainEdge`, `exact_MeasuredCombinedApplicationEdgeStepAt`,
  `exact_MeasuredCombinedRoundApplicationLeast`, `exact_CombinedLeastRepresentativeApplication`,
  `exact_MeasuredCombinedLeastRepresentativeApplication`. All axioms standard.
  Evidence `opusA/ROUND-APPLICATION-REPRESENTATIVE-EVIDENCE.json`; source map `opusA/ROUND-APPLICATION-SOURCE-MAP.md`.

## State and next (task 3)
All of (a), (b), (c) passed; nothing drafted-but-ungated. Remaining premises: for the unmeasured chosen exchange,
exactly `MeasurePreservingEdge (edge4 X W) (selectedMeasure P.R)` (false in general); for the measured
function-level exchange, none. Held inputs everywhere: two type guards, `windowAt W ctx dom arg`, the seed
application's least `m` (and for the round theorems the seed measure μ, always available by totality).
Not done: a single-exchange measured version (application least also over `Xm`). Route: measured analogue of
#1377 — D-lift by #1370 from the D-part of the measured edge, `compareMeasurements` at the applications from
`…PairedSharedMeasureParent` + #862-closure `compareShared`, `conjunctionAccept` to build `Dm(a,b)`, then
`guardedOfActualPair P.cover s Dm` (generic) — after which #818, #1338 and the round machinery apply unchanged.

## Task 4 — Paper 17 (stage emitter assembly)

- 16:24 Read fable2/PLAN.md (+ addenda), fable2/LEDGER.md turn 003, opusB/LEDGER.md, the Targets of
  StageCallbackSupplier/LevelOrder/RawLevel, RawPacketAlgebra{Join,Child}, RawProperClause, ActualRawStageCutoff,
  ActualBitFamilyRaw{Charts,Rank,Layout}, ClosedBlockDecision. Prefix `StageEmitter` unused.
- **Ownership note:** I (Opus A) own "effectivity of `rowCode R`" (Fable-2's turn-003 item 2) — not to be
  duplicated by Fable-2. Fable-2 keeps the rendering programs and their `Rendering.Exact` fields.
- Root: all of Opus B's packet algebra (#1404–#1408) is gated → used as theorems.
- **Frozen** `LogicLineages/PermittedControl/StageEmitterRowTargets.lean` sha256 `db7fd82678e96a78bd3b29c9474cdd8a4f97bfcffc03c81e5f5b5184f314d290` (compiled alone, receipt
  `1795386236385299359-3156047`): `RenderingEffective R` (four Primrec fields, uncurried exactly as Fable-2's
  `LinearCodeEffectivity`/modular effectivity last conjuncts), `ExactLevelCodeEffectivity`,
  `ExactSignedCodeEffectivity`, `ExactRowCodeEffectivity`.
- Gate FAIL ×3 on `StageEmitterRowProof` (receipts `1795386373221221170-3156433`, `1795386456638012616-3156813`,
  `1795386587909931500-3157199`, plus `1795386665328558569-3157448`): missing opens, untyped `Primrec.comp`
  arguments ("Primcodable ?m stuck"), a whnf timeout in the leaf lemma (fixed by splitting it into named
  `leafList`/`leafTip` pieces), and an `include` capturing R. Drafts kept in `drafts/opusA/StageEmitterRowProof-v*.lean.txt`.
- **Gate PASS** `StageEmitterRowProof` (sha `630f3f87780da0a6528b7a970633ad6ffa84bdbf3a0b57dae6b8991c65c0f081`),
  receipt `1795386686366038761-3157556`: `exactLevelCodeEffectivity`, `exactSignedCodeEffectivity`,
  `exactRowCodeEffectivity`, `fullStageEmitterRow`, axioms standard. Suppliers: `groupedPrimitive`,
  `groupRawPrimitive`, `labelsPrimitive`, `tapeHighestPrimitive`, `candidateTapesPrimitive`, `cleanupPrimitive`,
  `budgetCodeExact.1`, `IntegerAlgorithms.Proof.sign_primitive` (local copies of nonnegative/positive tests).
- **Frozen** `LogicLineages/PermittedControl/StageEmitterHighTargets.lean` sha256 `4bd3ab76cb81f64ec75f9ec1e7895bd6730afda81a9897c3d908cf051c507fd7` (compiled alone, receipt
  `1795386753170203185-3157818`): `chartCode`, `highCode` (exactly Fable-2's turn-003 formula, with
  `ActualBitFamilyRawCharts.charts`, `familyCode`, `properClausesCode`, `joinCode`, `rowCode R`, `childCode`),
  `ExactStageEmission`, `ExactHighCodeEffectivity`, `ExactConditionalEmitter`, `ExactConditionalClosedBlockDecision`.
- **Frozen** `LogicLineages/PermittedControl/StageEmitterGuardTargets.lean` sha256 `268d81c12fe6f217712fe22510c796ca041f2fefc24436b7d54ea54f6712cfc8` (receipt `1795386905417092047-3158425`).
- **Gate PASS** (all first attempt): `StageEmitterEmissionProof` (`1795386811723965461-3158006`, `exactStageEmission`),
  `StageEmitterEffectivityProof` (`1795386843288402976-3158147`, `exactHighCodeEffectivity`), `StageEmitterHighProof`
  (`1795386857356274355-3158225`, `exactConditionalEmitter`, `exactConditionalClosedBlockDecision`,
  `fullStageEmitterHigh`), `StageEmitterGuardProof` (`1795386914033320087-3158455`, `exactRenderingFromGuard`,
  `exactClosedBlockDecisionFromGuard`). All axioms standard. Evidence `opusA/STAGE-EMITTER-EVIDENCE.json`, source map
  `opusA/STAGE-EMITTER-SOURCE-MAP.md`.

## State and next (task 4)
Gated: `Emits levelOrder B (highCode R)` as a literal list equation for every B and every family (no use of
positive dimension; the raw charts equation #1336 is unconditional), Primrec/Computable `highCode R`, the
conditional emitter for every selected control, and the conditional `ClosedBlockDecision`.
**Exactly what stands between the repository and `ClosedBlockDecision`:** one program
`g : Nat → List LabelCode → List Nat → PreparedPacketCode` with
  `GuardExact g` : ∀ top grouped a, g top ((labels grouped).map encodeLabel) (a.map Answer.code)
                    = encodePacket (StageCallbackCanonicalRoutes.guard top grouped a)
  `GuardEffective g` : Primrec (fun p : Nat × List LabelCode × List Nat => g p.1 p.2.1 p.2.2)
(`exactClosedBlockDecisionFromGuard`). That is Fable-2's R1. Nothing else: append, linear, modular, row
iteration, join, residual, properness filter, rank, charts, names, level-order supplier and the #1396 reduction
are all used as gated theorems. No interface mismatch found. Nothing drafted but ungated.

## Task 5 — reading deliverables (no proofs)
- Wrote `opusA/P17-THM-ARITHMETIC-CORRESPONDENCE.md`: phrase-by-phrase table, read from definitions. Verdict:
  `ClosedBlockDecision` is the printed `thm:arithmetic` in the paper's flattened matrix language. The named
  conventions are: `PlainPreparedFormula` (atoms linear in node coordinates), universals over successful runs, and
  correctness only on encodings of topological circuits, where the answer is never `none`. The λ+k absorption is
  formalized (`ArbitraryFixedHeadCollapse.transported/ActualNormalization`).
- Wrote `opusA/P17-GROUND-GAP.md`: `thm:ground` is assembly only (M1 ground-domain lemma, M2 frozen statement,
  M3 positive-coordinate decider, M4 Scalar→circuit compiler, M5 decider) once `ClosedBlockDecision` is
  unconditional. `thm:generated-source` (#261) and `thm:functional-hardness` (#339, giving thm:main (ii)/(iii)) are
  already checked. Not started, pending root's go-ahead.

## Task 6 — thm:ground
- Root: `closedBlockDecision` unconditional (#1418). Prefix `GroundComparison` unused. Opus B owns M4 (`GroundScalarCircuit`).
- M1: **Frozen** `GroundComparisonDomainTargets.lean` sha256 `f2e62e2f4fd0c00269b60539a5970c6855c65ccccbd63cb3f8bc08aadcc730d0`
  (receipt `1795387652355466808-3162232`). **Gate PASS** `GroundComparisonDomainProof`, receipt
  `1795387681547037752-3162378`, `selectedGroundDomain` (copy of Paper 18's `DefaultSourceDomainProof.domain`, with
  `closed_scalar_finite`/`closed_positive` at the selected control).
- M2: **Frozen** `GroundComparisonTargets.lean` sha256 `1c4d40201de55c3f03f145914bb44ccd75de641fc2b59038c09de9931b6e2d91`
  (receipt `1795387711612798636-3162507`): `Relation`, `vectorAt` (zero padding), `Holds`, `Canonical`,
  `GroundDecidable`, `GroundComparison`. Interface for Opus B written: `opusA/GROUND-INTERFACE-FOR-M4.md`.
- M3: **Frozen** `GroundComparisonPositiveTargets.lean` sha256 `29d83ea6e154ec6a5d5b651d350715969e830eddd621065d18b7d6f02594d99e`
  (receipt `1795387797898352199-3162871`). One FAIL (`1795387846072722323-3163019`, universe of a helper), then
  **Gate PASS** `GroundComparisonPositiveProof`, receipt `1795387863484361049-3163145`:
  `exactPositiveTest`, `positiveTestEffectivity`, `fullGroundComparisonPositive`.
- Reduction: **Frozen** `GroundComparisonReductionTargets.lean` sha256 `c6b1adb1d3a4f26c57a56dbb07c32f3cb3ec0d9b6e35841561bf5210c641ad6d` (receipt `1795388072799379934-3163876`): `idx`, `tagOf`, `equalFlag`, `ExactCanonicalReduction` (uses Opus B's frozen `GroundScalarCircuit.Counter`).
- **Gate PASS** `GroundComparisonReductionProof` (sha `235f804c…6188`), receipt `1795388167211519221-3164178`: `exactCanonicalReduction` (Canonical ↔ raw positive test ∧ no positive scalar counterexample), standard axioms.
- thm:main: **Frozen** `GroundComparisonMainTargets.lean` sha256 `c3552aad4b8e882f9b507473da60d39081ca38256f321291670fb1e84329ac4f` (receipt `1795388204050892648-3164395`): `MainComparison := FullControl ∧ NearControlModular ∧ GroundComparison ∧ SelectedFunctionalHardness`. 'Permitted' traced: no Lean predicate exists; paper foundations.tex l.81–88 defines the framework as 'computable strictly increasing f ≥ G' with the constructed controls 'also primitive recursive, growth, eventual bound' — all clauses of `ControlLaws` (#010).
- Assembly: **Frozen** `GroundComparisonAssemblyTargets.lean` sha256 `c8b3264be210f65890a21654b09c4c64fbbce3a6bdac9537fd7a6b7b97675e23` (receipt `1795388264598927755-3164645`): `QueryInterface query` (verbatim the M4 interface), `ExactGroundFromQuery` (∀ query meeting it, computable → GroundComparison). Lets M5 be gated before Opus B's code-level compiler lands.
- Gate FAIL `GroundComparisonAssemblyProof` v1 (`1795388334098976752-3164843`, defeq timeouts; draft kept). **Gate PASS** v2,
  receipt `1795388401995430418-3165135`: `exactGroundFromQuery` — `GroundComparison` from any computable compiler
  meeting `QueryInterface` (uses #261 `typedImage`/`Programs`, M1, M3, the reduction, `scalarSyntaxNormalizationCorrect`,
  and `StageCallbackGuardRender.closedBlockDecision`). Standard axioms.
- Opus B's M4 gated (#1423; `GroundScalarCircuit.exactQueryCode`, `queryCodeEffectivity`), frozen to my interface verbatim.
- **Gate PASS** `GroundComparisonProof` (sha `10b685ac…8691`) and `GroundComparisonMainProof` (sha `638f40ab…d910`), receipt
  `1795388718263284980-3166116`: `GroundComparison.groundComparison : GroundComparison` and
  `GroundComparisonMain.mainComparison : MainComparison`, both unconditional, axioms `[propext, Classical.choice, Quot.sound]`.
  Evidence `opusA/GROUND-COMPARISON-EVIDENCE.json`; tables `opusA/P17-THM-GROUND-CORRESPONDENCE.md`, `P17-THM-MAIN-CORRESPONDENCE.md`.

## State and next (task 6)
thm:ground and thm:main comparators are unconditional gated theorems. Register untouched (root/owner). Nothing drafted
but ungated. Named readings for the owner: zero padding of different-length vectors; one decider per
policy/control/relation, correct on encoded typed terms; "permitted" carried by `lem:control`'s clauses (no Lean
predicate for WW §2.1 exists or is claimed).
