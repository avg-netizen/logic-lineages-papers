# Opus B ledger, round 3 (22 Nov)

Task (Root): compile the drafted native statements parked on the import boundary, on module-system twins.
Rules: gate only via `verification/local-fable-pair-2026-11-22-round3/gate.sh`; no git; no edits to tracked
files (round-2 twins, generator and manifest are tracked — round-3 copy of the generator in `opusB/twin/`
skips existing twins after checking them by hash against the round-2 manifest; new entries go to
`opusB/twin/TWIN-MANIFEST-ROUND3.json`). Round-2 wording correction: eight files, nine `private` removals.

- Round-2 manifest re-hash at start: 671 twins, 0 mismatches.
- Item 1a GuardedNorm: 8 new twins (item-1 closure 438, 424 round-2 twins skipped after hash check).
  Gate 1 FAILED (receipt `1795401972104081482-3274832`): never-compiled draft `scalarLaw` — `rw [stageEq]`
  cannot see `stage` under abbrev `ordinalStage`; its closing `rfl` would also equate `∃ _ : b < a` with
  `b < a ∧`. Repaired in the twin (show / rw / `simp only [exists_prop]` / rfl; manifest diff).
  Gate 2 PASSED: receipt `1795402033770287946-3275204`, twin `NumberedWindowGuardedNormProof`, peak RSS
  882,444 KiB. `exact_ActualScalarStageRank`, `exact_ActualScalarOrdinalNorm`, `exact_IsolatedAdmittedAddressStarts`;
  axioms [propext, Classical.choice, Quot.sound].
- Rule slip: I created an empty scratch file `opusB/twin/make_twins.py.patch` by mistake and removed it with
  `rm -f` in the same command. It held no data; reported to root.
- Item 1b AddressClassRank PASSED first try: receipt `1795402055383415156-3275283`, twin
  `NumberedWindowAddressClassRankProof`, peak RSS 906,848 KiB. `exact_ActualAddressClassRankEquality`,
  `exact_ActualClassStageNormAtAddress`; axioms [propext, Classical.choice, Quot.sound]; no sorryAx.
- Item 2a ArithmeticComposition: 18 new twins (closure 682, 653 round-2 twins skipped). PASSED first try:
  receipt `1795402092285333664-3275481`, twin `NativeOrdinalArithmeticCompositionProof`, peak RSS 936,340 KiB.
  `exact_LiteralNativeArithmeticRealizes`; axioms [propext, Classical.choice, Quot.sound]; draft unchanged.
- Item 2b: `NativeOrdinalArithmeticRealizationTargets` has no proof draft. Target frozen (twin sha256
  641f4a068e9a0c0b92c66766351fd041f6edf9b3e395446a9b88289bf18c455d). New proof module (not a twin)
  `LogicLineages/NativeModule/PersistentMarking/NativeOrdinalArithmeticRealizationProof.lean` from 2a +
  `exact_OrdinalArithmeticOrbits` + `exact_OrdinalOmegaOrbits`.
- Item 2b PASSED first try: receipt `1795402162170917672-3276046`, new module
  `NativeOrdinalArithmeticRealizationProof`, peak RSS 931,092 KiB. `exact_NativeOrdinalArithmeticRealization`;
  axioms [propext, Classical.choice, Quot.sound]. (Module-system originals `OrdinalArithmeticOrbitProof`,
  `OrdinalOmegaOrbitProof` compiled fresh in this gate, rc 0.)
- Item 3a ArithmeticPairProgramChecks: closure 18 (6 legacy; 5 new twins). PASSED first try: receipt
  `1795402204639313192-3276260`, peak RSS 855,372 KiB. `exact_PairAndDecodeCalibration` [propext, Quot.sound],
  `exact_ActualPairProgram`, `exact_ActualPairDecoderProgram` [propext, Classical.choice, Quot.sound]. Drafts unchanged.
- Item 3b PairEvaluation: closure 9 (4 legacy; 2 new twins). PASSED first try: receipt
  `1795402232822083563-3276404`, peak RSS 849,980 KiB. `exact_ActualPairProgram`, `exact_ActualPairDecoderProgram`
  [propext, Classical.choice, Quot.sound]. Drafts unchanged.
- Item 3c SparseDecode: closure 1039 (6 legacy; 2 new twins). Gate 1 FAILED (receipt
  `1795402249793041701-3276457`) and gate 2 FAILED (`1795402309139999234-3276731`) in the never-compiled twin
  `NumberedWindowInternalSparseDecodeEvaluationProof`. Five one-line repairs (manifest diffs):
  `symm` before `Nat.eq_sqrt.mpr` (pinned lemma states `a = sqrt n`); `dsimp only` after `unfold chosenDecode`
  (a `have` binder hid the rewrite pattern); three steps where the draft mixes the two identical, exposed
  copies of the pairing (`NumberedWindowPairAlgorithm` vs `NumberedWindowArithmeticPair`) — `exact` up to
  definitional equality instead of `simp`/`rw`, and unfold the right name. Gate 3 PASSED: receipt
  `1795402353896996749-3277001`, peak RSS 1,036,584 KiB (module-system original `…SparseDecodeFailureProof`,
  compiled fresh); twins `…EvaluationProof` 1,017,276, `…Checks` 1,029,516. `exact_CandidateValues`,
  `exact_GuardValue`, `exact_AllInputDecoder`, `exact_OpenSuccess`, `exact_OpenFailure`
  [propext, Classical.choice, Quot.sound].
- Item 3d FreshProbeDispatchOriginalIntegrationTargets: closure 976 (137 legacy; 8 new twins). Targets twin
  PASSED first try: receipt `1795402393988330714-3277234`, peak RSS 1,033,832 KiB. It contains only the two
  definitions `ExactOriginalSelectedProbeTypedTotal`, `ExactOriginalConcreteProbeTypedTotal`; no proof draft
  exists anywhere in the tree (source map only). STOP on proving them: each asserts arbitrary-open ID₁
  typed-probe totality (`TypedProbeTotal` for every derivation of `typedAt h (σ→τ) q`) — the internal
  fresh-variable step of lem:arithmetic-accessibility, new mathematics, not attempted.
- End state: round-3 manifest 43 new twins, 2 changed bodies (6 one-line repairs); round-2 manifest 671
  twins re-hashed, 0 mismatches; new non-twin module `NativeOrdinalArithmeticRealizationProof`.
- Wrote opusB/P16-THM-UPPER-CHAIN-CORRESPONDENCE.md (reading deliverable, no gates).
- Joining lemma (Root): new module-system files (not twins)
  `LogicLineages/NativeModule/PersistentMarking/NumberedWindowConfinedRankStageNormTargets.lean` — frozen and gated
  first (receipt `1795402772811303646-3279080`, 890,840 KiB; sha256 fbc8dfa61a22f3af2cd48e0a4a6899c396b7083077a2413a4a2bc6c2900d730b)
  — and `…StageNormProof.lean` (sha256 6d17af3765970f87406d1ea8c3beedf5b6a3cb9d6742ae383d62a0e781ac46b6).
  PASSED first try: receipt `1795402793153913589-3279202`, 448 modules, proof module 905,672 KiB (gate peak
  906,848 at cached `NumberedWindowAddressClassRankProof`). `exact_ConfinedRankBelowTaggedStageNorm :
  ConfinedRankBelowTaggedStageNorm`, axioms [propext, Classical.choice, Quot.sound], no sorryAx. Pure assembly
  of #1448 + #1455 at Γ = [] (definitional `finiteC [] = EmptyContext`; Acc-rank congruence by proof
  irrelevance). The norm side is the class/address side where #1455 holds; the fixed-type-versus-whole-universe
  rank equality is neither used nor claimed.
