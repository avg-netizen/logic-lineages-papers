# `FreshApplicationTotal`: what remains of the arrow branch, and why it was not forced

Fable B, 27 November 2026. Names without a path are under
`LogicLineages/PersistentMarking/`; `P16…` abbreviates
`LogicLineages/NativeModule/PersistentMarking/Paper16AccessibilityMilestone…`.

## The obligation

`P16…ArrowTypingTargetsV2.FreshApplicationTotal A c`: for σ→τ in the window, from

- `carrier A.presentation false c q`,
- `storedType (σ→τ) q` (the result field of `q` is the literal code of σ→τ),
- `freshAt (chosenA A.probes) q u` (the fresh selector returned `u`),

derive `∃ v (accepts A.probes.applicationGuard q u v ∧ storedType τ v)`.

With it, `CarrierTypingCases` holds on the window with literal probe leaves
(`exact_TypingCasesFromReports`, `exact_StackedLiteralProbeReports`,
`exact_WindowReductionFromJoinedFacts`). Without it the arrow branch cannot be introduced: the
checker `chosenH` runs the ternary guard on the fresh address, so its acceptance *is* an accepted
application.

## Why no existing theorem supplies it

Every checked internal law that concludes an application acceptance has one as a premise:

- `ForwardRule` (`exact_OpenJoinedForwardRule`): from `accepts f u x` and an edge `f → g`.
- `TypedProbeTotal` / `AlignedCarriersAt`: from `typedAt (σ→τ) q`, i.e. from the conclusion wanted here.
- `exact_OpenGuardedApplication`: an equivalence between acceptance and `applicationReport`.
- `exact_OpenLiteralApplicationFromReportedLeast`
  (`NumberedWindowInternalLiteralApplicationRebuildProof.lean`): acceptance of
  `applicationGuard i L` at `(f, u, y)` from the two address reports, the two scalar acceptances,
  `programGraph L (suc k) ![ctx, cod, auxiliaryTerm dom cod fn arg]`, and `y = addressTerm ctx cod k`.

The last one is the right introduction rule. Feeding it for `f = q`, `u = packedFreeTerm ctx dom name`
leaves exactly two facts that are not consequences of the carrier of `q`:

1. **K1, carrier of the fresh address.** `packedFreeTerm ctx dom name` is definitionally
   `addressTerm ctx dom payload` with `payload = consTerm 0 (consTerm dom (consTerm name 0))`.
   `exact_OpenLiteralScalarFromSelfLeast` (`NumberedWindowInternalLiteralCanonicalChildProof.lean`)
   gives the address scalar at a literal address from the two validators, `windowAt W ctx dom payload`,
   and the self-least report `programGraph L (suc payload) ![ctx, dom, payload]`. The context
   validator comes from `q`; the type validator at the literal domain code is a closed numeral
   fact; the stored-type filter is literal. Open: the window test and the self-least report at the
   variable payload.
2. **K2, a least representative for the application seed.**
   `programGraph L (suc k) ![ctx, cod, auxiliaryTerm dom cod fn payload]` for some `k`.

Both are *positive totality* facts about the installed least program
`L = memoFilteredLeast C Base s = guardedLeast (headerLeast (fullAuxiliaryDecorator (packedLeastOn C (recursiveTypedMemo Base) s)))`
(`NumberedWindowInternalLiteralTypedMemoLeastLawsProof.lean`), where
`packedLeastOn C E s = branch contextOption 0 (scratchMinimum (members E (poolAtSeed C s), …))`
(`NumberedWindowInternalLiteralPackedLeastOnProof.lean`). A successor output needs, inside the
calculus: the context option succeeds, the member list of the seed's class in the cover pool is
nonempty, and the guards of `guardedLeast` / `headerLeast` pass
(`MemoSelectedReports` already transfers an unguarded `leastOnGraph` to the guarded program).
The cover `C`, the base memo and the syntax program are packet witnesses with numeric calibration
and a list of open laws (`reverse`, `ends`, `stable`, `selected`, `guards`); none of those laws
produces a first member. This is the round-6 lesson in a sharper form: the code of `L` is visible
down to `members`/`scratchMinimum`, and the missing statement is an internal "the seed is a member
of its own class when it is in the pool", for the two seed shapes above.

Once K2 is derived, the rest of `FreshApplicationTotal` is finite-shape and has suppliers:
`exact_OpenAddressArrowCoordinates` (result field of `q` is `rawCons dom cod`), the cell reports at
the literal arrow code as in `exact_ReinstalledFreshExists`, `exact_OpenAtomicRecognition.1`
(fields of the packed free address), and the field reports of `addressTerm ctx cod k` for the
stored type of the result.

## Why the guard device does not apply

Round 6 closed `NilNoStep` by guarding a checker with a visible test. The analogous move here is
to conjoin the probe tree to the scalar carrier, which makes `CarrierTypingCases` immediate. It
fails for a structural reason: the scalar carrier must be *produced* for new arrow-typed
addresses by `ApplicationOutput` (result carrier of every accepted application) and inside
`ForwardRule` (the image application). A guarded carrier at an arrow-typed result `t = x u`
would assert that `t` applied to its own fresh address is accepted — again K1/K2, now for an
arbitrary application result, with no premise to draw it from. Guarding the application program
instead moves the same demand into `ForwardRule`. So the fact has to be derived, not guarded.

## Consequence for `ApplicationArithmetic.matchEdge`

Backward matching (`ApplicationEdgeMatching`) needs `accepts f u w` from an edge `f → g` and
`accepts g u v`: the same kind of first acceptance (K2 at the seed of `f u`), plus the congruence
edge `w → v`. `exact_CloseAllTerms` does not consume `matchEdge`, and
`exact_WindowReductionFromJoinedFacts` does not take `ApplicationArithmetic` at all, so the
all-terms assembly is independent of it. Whether `TypedCarrierComputability` will need downward
closure in the matching form is the beta/lambda lanes' design question; their current rules use
the inherited-application inversion instead.

## Suggested next step

Derive, for the joined packet's programs, the internal law

`windowAt W ctx ty seed ∧ (cover pool contains seed) ⊢ ∃ k, leastOnGraph C E s ctx ty seed k`

by list induction over the pool in the `members` recursion (first member = the seed itself, using
the reflexive case of the edge memo), then instantiate it at the variable payload (K1) and the
application seed (K2). `SelectedSeedFormation`
(`NumberedWindowInternalLiteralApplicationFormationSeamProof.lean`) is the existing statement of
the window half for application seeds.
