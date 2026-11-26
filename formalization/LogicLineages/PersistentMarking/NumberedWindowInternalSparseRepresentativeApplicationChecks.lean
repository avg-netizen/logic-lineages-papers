module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRepresentativeApplicationTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRepresentativeApplicationClosureProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundObservationChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseStructuralApplicationChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRepresentativeApplicationChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons suc)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseRoundObservationChecks (exact_SelectedObservation)
open NumberedWindowInternalSparseRepresentativeApplicationTargets
open NumberedWindowInternalSparseRepresentativeApplicationClosureProof (localClosure)
theorem exact_ApplicationObservation : ExactApplicationObservation :=
  NumberedWindowInternalSparseRepresentativeApplicationGraphProof.observerGraph

theorem exact_RepresentativeApplication : ExactRepresentativeApplication := by
  intro C s X W law body α Γ ctx dom cod arg f repr value initial chosen final
  let least := packedLeastProgram C X W s
  let M := applicationObserver least
  let A := supports C X W s ctx dom cod arg value ⊓ (initial ⊓ chosen)
  let Δ := A :: Γ
  have h : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  obtain ⟨closed⟩ := localClosure C s X W law ctx dom cod arg value ⟨Derivation.conjunctionLeft h⟩
  have runs := Derivation.conjunctionRight h
  obtain ⟨src⟩ := (exact_ApplicationObservation least body α Δ ctx dom cod arg f (suc value)).mpr
    ⟨Derivation.conjunctionLeft runs⟩
  obtain ⟨move⟩ := exact_SelectedObservation C X W s M body α Δ ctx (rawCons dom cod) dom cod arg f repr (suc value)
  have target := Derivation.implicationElimination move (Derivation.conjunctionIntroduction
    (Derivation.conjunctionIntroduction closed src) (Derivation.conjunctionRight runs))
  obtain ⟨out⟩ := (exact_ApplicationObservation least body α Δ ctx dom cod arg repr (suc value)).mp ⟨target⟩
  exact ⟨Derivation.implicationIntroduction out⟩

#print axioms exact_ApplicationObservation
#print axioms exact_RepresentativeApplication
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRepresentativeApplicationChecks
