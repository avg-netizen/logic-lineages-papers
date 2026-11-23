module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicMembershipTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementReinstallTargets
public import LogicLineages.PersistentMarking.NumberedWindowAtomicPositiveTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAtomicNumeralAdmissionTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation (sourceBody)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowAtomicPositiveTargets (bottomAddress freeAddress)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings scalar)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs)
open NumberedWindowInternalAtomicRefinementReinstallTargets (TupleAt)
open NumberedWindowInternalAtomicRefinement (refined)
open NumberedWindowInternalPresentationTargets (data)

/-- Admitted atomic numerals yield real finite object proofs on the same body
as the refined selected tuple, without a supplied object carrier derivation.
The outer arithmetic context and hypotheses may vary; the packed fields
of the address itself are numerals. -/
def CutAt (s : Settings) (i j : Program 1) (r d : Program 3) : Prop :=
  ∀ (c : Nat) (α : Type) (Γ : List (Formula α)),
    let B := sourceBody (data i j (refined i r) d) c
    (∀ ctx t : Nat, scalar s (bottomAddress ctx t) = true →
      Nonempty (Derivation B Γ (membership false (numeral (bottomAddress ctx t))))) ∧
    (∀ ctx t n : Nat, scalar s (freeAddress ctx t n) = true →
      Nonempty (Derivation B Γ (membership false (numeral (freeAddress ctx t n)))))

def ExactSelectedAtomicNumeralAdmission : Prop :=
  ∀ (xs : Entries) (s : Settings) (W : List ProbeTy), ValidWindow s W →
    ∃ (i j : Program 1) (r d : Program 3) (v : Inputs),
      TupleAt xs s W i j r d v ∧ TupleAt xs s W i j (refined i r) d v ∧ CutAt s i j r d

end LogicLineages.PersistentMarking.NumberedWindowInternalAtomicNumeralAdmissionTargets
