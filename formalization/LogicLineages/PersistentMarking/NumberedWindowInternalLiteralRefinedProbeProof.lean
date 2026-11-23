module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRefinedScalarTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalGroundFreshTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTypedObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowGuardedGraphChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentCarriersProof
import LogicLineages.PersistentMarking.NumberedWindowInternalGroundFreshMembershipProof
import LogicLineages.PersistentMarking.NumberedWindowInternalPullbackChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRefinedProbeProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalLiteralRefinedScalarTargets (refinedLiteral)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ChildClosed)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs chosenH chosenA)
open NumberedWindowInternalFreshProbeParsedTypedObjectChecks (exact_SameParsedTypedProbeTotal)
open NumberedWindowInternalFreshProbeAlignmentCarriersProof (carriers)
open NumberedWindowInternalGroundFreshMembershipProof (givenFreshMember)
open NumberedWindowInternalGroundFreshTargets (GroundFreshAt)
open NumberedWindowInternalProbeTargets (TypedProbeTotal)
open NumberedWindowGuardedGraphTargets (guard InputGuards)
open NumberedWindowGuardedGraphChecks (exact_GuardRules)
open NumberedWindowInternalAtomicRefinement (refined)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalPullbackTargets (ForwardRule Pullback)
open NumberedWindowInternalPullbackChecks (exact_InternalPullback)

/-- The physically chosen parsed probe programs are interpreted directly
in the literal refined scalar/list body. No old tuple is transported. -/
theorem typedProbe (i : Program 1) (r : Program 3) (v : Inputs) (W : List ProbeTy)
    (closed : ChildClosed W) (c : Nat) :
    TypedProbeTotal (refinedLiteral i r) v.applicationGuard (chosenH v W) (chosenA v) c :=
  exact_SameParsedTypedProbeTotal v W closed (refinedLiteral i r) c

private theorem guardInLiteral (i : Program 1) (r p : Program 3) (v : Inputs)
    (exactGuard : v.applicationGuard = guard i p) :
    InputGuards i (jRaw i) (refined i r) (dCore i (refined i r) permutation) v.applicationGuard := by
  rw [exactGuard]
  exact (exact_GuardRules i (jRaw i) (refined i r) (dCore i (refined i r) permutation) p).1

/-- The actual given-u, ground-domain probe is computable in the same body.
Its carrier follows from the physically guarded application at this u;
the original free-shape result, rather than an assumed atom, gives I(u). -/
theorem groundFresh (i : Program 1) (r p : Program 3) (v : Inputs) (W : List ProbeTy)
    (closed : ChildClosed W) (exactGuard : v.applicationGuard = guard i p) (c : Nat) :
    GroundFreshAt (refinedLiteral i r) v.applicationGuard (chosenH v W) (chosenA v) c := by
  intro τ α Γ q u ht ha
  have aligned := carriers i (jRaw i) (refined i r) (dCore i (refined i r) permutation)
    v.applicationGuard (chosenH v W) (chosenA v) c (guardInLiteral i r p v exactGuard)
    (typedProbe i r v W closed c)
  obtain ⟨facts⟩ := aligned .ground τ α Γ q u ht ha
  exact givenFreshMember i (jRaw i) r (dCore i (refined i r) permutation) v c α Γ q u ha
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight facts)⟩

/-- Only the genuine arithmetic forward image of positive function paths
remains a premise of the accessibility pullback, not the pullback itself. -/
theorem pullbackOfForward (i : Program 1) (r p : Program 3) (v : Inputs)
    (exactGuard : v.applicationGuard = guard i p) (c : Nat)
    (forward : ForwardRule (refinedLiteral i r) v.applicationGuard c) :
    Pullback (refinedLiteral i r) v.applicationGuard c :=
  exact_InternalPullback i (jRaw i) (refined i r) (dCore i (refined i r) permutation)
    v.applicationGuard c (guardInLiteral i r p v exactGuard) forward

#print axioms typedProbe
#print axioms groundFresh
#print axioms pullbackOfForward
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRefinedProbeProof
