# Opus B ledger, round 5 (22 Nov)

Task (Root): bridge from the uniform all-terms accessibility sentence to the individual atom `thm:upper` uses
(prefix `ConditionalUpperUniform`): (i) ∀-elimination at the address numeral, (ii) internal Σ₁-truth of the scalar
checker graph at the numeral, (iii) `tagTerm false (numeral x) = numeral (2x)`; then re-close `thm:upper` and
`thm:main` with the uniform hypothesis. Rules: round-5 gate, no git, no rm, never edit existing .lean files.

- Goal-statement check. No Paper-16 record states derivability of the all-terms sentence. #571's target is
  `NumberedWindowInternalAccessibilityChecks.exact_ConcreteInternalAccessibility` (programs with `Evaluates`,
  `Interprets`, `Rules` — the presentation and its (A) rules); #573's is
  `NumberedWindowOriginalAdmittedTaggedChecks.exact_AllAdmittedInTaggedLeast` (standard-model truth); #585/#599 are
  aimed at `membership false x` derivations for terms x. The derivability goal `Nonempty (Derivation (sourceBody d c)
  [] (allTermsFormula d c))` is stated (PENDING) by the shared ID1Completion line: Paper 06's
  `SourcePresentationTargets.ActualSourceInternalAccessibility` / `ContextUniformTargets.ActualContextUniformInternalAccessibility`,
  and verbatim by Opus A's `ExternalOrdinalInterfaceID1Targets.InternalAccessibility d c`.
- Suppliers found: (ii) `InternalNumeralEvaluationStatementChecks.numeral_evaluation_exact`
  (`ActualOriginalNumeralEvaluation`: a derivation of `graph (graphFormula p) (numeral (evaluate p v)) (numerals v)`
  for every program and input), `NumberedWindowCheckerCoordinatesProof.exact_ExactCoordinates`; (iii)
  `InternalTagArithmeticSupportProof.{doubleZero, doubleSucc, congSuc, trans}`; (i) `Derivation.universalElimination`
  plus the syntax lemmas `formulaSubstComposition`, `embedSubst`, `numeralSubst`, `membershipSubst`, `predicateSubstitution`.
- `ConditionalUpperUniformTargets` frozen after two compile-fix attempts on the draft (missing `α := Empty`,
  missing `open PositiveArithmeticTransforms`; failed receipts `1795405358022371133-3294604` and the one before it):
  sha256 cdb68486803a78a3998c1fdfa8eff6c45ff677811d303350b7b7bd32c43333e8, receipt `1795405370299456044-3294639`, 1,073,808 KiB.
- (iii) `ConditionalUpperUniformTagProof.exact_EvenTagNumeral` PASSED: receipt `1795405399179687850-3294761`, 1,079,424 KiB, [propext, Quot.sound].
- (i) `ConditionalUpperUniformInstanceProof.exact_AllTermsInstance` PASSED: receipt `1795405423235299499-3294855`, 1,101,468 KiB, [propext, Quot.sound].
- (ii) `ConditionalUpperUniformCarrierProof.exact_ScalarCarrierNumeralTruth` PASSED: receipt `1795405447609717273-3294906`, 1,092,796 KiB, [propext, Classical.choice, Quot.sound].
- Bridge `ConditionalUpperUniformBridgeProof.exact_UniformToIndividual` PASSED (after one missing-`open` fix, failed
  receipt `1795405487615989337-3295049`): receipt `1795405499583388240-3295092`, 1,124,748 KiB, [propext, Classical.choice, Quot.sound].
- `ConditionalUpperUniformProof.exact_ConditionalUpperUniform` PASSED: receipt `1795405517923316778-3295168`, 1,797 modules,
  1,140,520 KiB. `ConditionalUpperUniformMain16Proof.exact_ConditionalMain16Uniform` PASSED: receipt
  `1795405528567519678-3295201`, 2,207 modules, 1,174,552 KiB. Both [propext, Classical.choice, Quot.sound]; no sorryAx in
  any passing log. No new twins were needed this round (all suppliers module-system or already twinned).
