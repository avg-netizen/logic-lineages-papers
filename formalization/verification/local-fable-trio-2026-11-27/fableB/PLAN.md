# Fable B plan — internal accessibility lane (27 November 2026)

Goal: checked progress on the three premises of
`Paper16AccessibilityMilestoneAllTermsAssemblyV2.exact_CloseAllTerms`
(`CarrierTypingCases`, `ApplicationArithmetic`, `TypedCarrierComputability`), or on the multiset
checkpoint, for Paper 16 `lem:arithmetic-accessibility`. Module names below carry the prefix
`LogicLineages.NativeModule.PersistentMarking.` unless a path is given.

## What the reading showed

1. **`FinishMultisets` is a pure logical consequence of existing derivations.**
   `ConditionalJSingletonProof.exact_ConditionalJSingleton` / `exact_ConditionalJMembers` use their
   `CarrierUnion` and `MultisetSplit` premises only to obtain `UnionClosure`. On an installed
   window, `UnionClosure` follows from `CertifiedMultisetUnion.union` (the literal J-union under the
   certified origin split) and `MultisetGeneration.unionReport`, with the two carriers extracted
   from the J-memberships (`actualOriginalCarrierExtraction`). Done first (item A).
2. **On the joined lambda window, three of the four `ApplicationArithmetic` fields are already
   theorems, and the assembly does not consume the fourth.**
   `exact_InstalledLambdaWindowWithScalarAtOriginalWindow`
   (`Paper16AccessibilityMilestoneInstalledLambdaWindowV2`) returns
   `BetaJoinedRulesAt A.presentation …` whose fields `forward`, `fresh`, `typedComputableToMember`
   are `ForwardRule`, `FreshVariablesComputable`, and the conclusion of
   `TypedComputabilityImpliesMembership` on that presentation; `TypedProbeTotal` is component 9 of
   the installed tuple. `exact_CloseAllTerms` never uses `ApplicationArithmetic.matchEdge`.
   `matchEdge` (`ApplicationEdgeMatching`, round-6 M1) has no proof on the installed presentation
   and needs, at least, an application result for `f u` given one for `g u` (see 4).
3. **The arrow branch of `CarrierTypingCases` is a finite-shape composition, except for one fact.**
   `typedAt (chosenH A.probes W) (σ→τ) q` is acceptance of a checker that runs the prior type
   test, the fresh selector, the binary option application, the ternary guard, and itself at τ.
   Checked suppliers exist for every piece once the probe leaves are the literal ones
   (`retypeWindow`, `reinstallFreshScalar`, `reinstallOptionApplication`):
   - stored type in the finite window: `exact_OpenLiteralFiniteScalar`, `memberToChoices`;
   - prior typing: `priorTypedOf`, `exact_RequestedTypeTestFromResult`, `exact_DomainRules`;
   - fresh report: `exact_ReinstalledFreshExists`;
   - option report from an accepted guard: `exact_ReinstalledOptionApplicationReport`;
   - result carrier: `BetaJoinedRulesAt.applicationOutput`;
   - arrow introduction: `exact_OriginalArrowTypedIntroduction`.
   What no existing theorem supplies is **an accepted ternary application at the fresh address**
   (and the stored type of its result): `FreshApplicationTotal` below.
4. **Why that fact is not a guard away.** Every existing internal theorem that concludes an
   application acceptance takes another acceptance as a premise (`ForwardRule`, typed-probe
   totality from `typedAt`). Acceptance at `(q, u)` unfolds
   (`exact_OpenGuardedApplication`) to a successor output of the installed least program on the
   auxiliary seed `aux(dom, cod, fn, arg)` plus scalar acceptance of the fresh address, whose
   `coordinateCall` is again a successor output of the least program on the packed free
   coordinate. The installed least program is
   `memoFilteredLeast C Base s = guardedLeast (headerLeast (fullAuxiliaryDecorator (packedLeastOn …)))`
   and `packedLeastOn` is `branch contextOption 0 (scratchMinimum (members E (pool …)))`: a
   successor output needs an internal proof that the member list of the seed's class is nonempty.
   Adding the probe tree as a guard on the scalar carrier would make `CarrierTypingCases`
   immediate but breaks `ApplicationOutput` (result carrier) and `ForwardRule`, which must
   *produce* carriers of new arrow-typed addresses; so the guard device of round 6 does not apply
   here. Recorded in `FRESH-APPLICATION-REPORT.md`.

## Agenda

A. `FinishMultisets` (frozen in `Paper16AccessibilityMilestoneTargetsV2`).
   New module `Paper16AccessibilityMilestoneFinishMultisetsV2`:
   `exact_SingletonFromUnionClosure`, `exact_MembersFromUnionClosure` (the two round-6 inductions
   rerun from `UnionClosure`), `exact_UnionClosureFromCertified`, `exact_FinishMultisets`.
   No new arithmetic.

B. `CarrierTypingCases` at arrow types, reduced to `FreshApplicationTotal`.
   - Freeze `Paper16AccessibilityMilestoneArrowTypingTargetsV2`: `storedType`,
     `storedTypeChoices`, `typedResultAt`, `FreshApplicationTotal`, `ApplicationResultCarrier`,
     `LiteralProbeReports` (five open report rules), `StoredTypeTyping`,
     `StoredTypingFromReports`, `TypingCasesFromReports`.
   - `Paper16AccessibilityMilestoneArrowTypingProofV2`: `exact_StoredTypingFromReports` by
     external recursion on the type (ground: the ground introduction; arrow: two existential
     eliminations, recursive call at the codomain, `exact_OriginalArrowTypedIntroduction`), and
     `exact_TypingCasesFromReports` by elimination of the finite stored-type disjunction.
     New derivations: n-ary disjunction elimination, renaming of `storedType`.
   - Freeze `Paper16AccessibilityMilestoneArrowTypingInstallTargetsV2`: `literalProbeWindow`
     (the three reinstallations stacked), `StackedLiteralProbeReports`,
     `InstalledAccessibilityReduction`.
   - `Paper16AccessibilityMilestoneArrowTypingInstallProofV2`: the five reports on
     `literalProbeWindow A` from the finite scalar shape, `A.application = applicationCore A.least`
     and the result carrier. New derivation: literal code choices to stored-type choices.

C. Assembly on the joined lambda window
   (`Paper16AccessibilityMilestoneArrowTypingSelectionProofV2`): for every closed `K` one
   installed window `B` with, for all `c`,
   `FreshApplicationTotal B c → CarrierTypingCases B c` and
   `CarrierTypingCases B c → TypedCarrierComputability B c → AllTerms B c`
   (the second without any `ApplicationArithmetic` premise: forward rule, typed probe and fresh
   computability are rebuilt on `B` from the joined rules, as in the coordinator's
   `exact_BetaJoinedRulesAfterRetype`). Depends on
   `Paper16AccessibilityMilestoneInstalledLambdaWindowV2`, which had no passing receipt at the
   start of the round (3,900-module closure); gate only after root reports it.

## Not attempted

- `FreshApplicationTotal` itself (internal totality of the least program on the application seed
  and on the packed free coordinate).
- `ApplicationArithmetic.matchEdge` (M1).
- `TypedCarrierComputability` (neutral / lambda / constructor / structural inductions; the beta and
  lambda lanes of 26 November own the lambda case).
- The premises of `FinishMultisets` (`CertifiedMultisetUnion`, `MultisetGeneration`).
