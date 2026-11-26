module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedScalarAuxTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrappedAuxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrappedAuxInputsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeOpenChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedScalarAuxProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalCoverCombinedRestrictedWrappedAuxProof (exact_OpenCoverCombinedWrappedAuxFormation)
open NumberedWindowInternalCoverCombinedRestrictedWrappedAuxInputsProof (exact_OpenCoverThinMatchingWindowInputs)
open NumberedWindowInternalSparseScalarEdgeOpenChecks (exact_OpenPackedScalarEdge)
open NumberedWindowInternalCoverCombinedRestrictedScalarAuxTargets

theorem exact_OpenCoverCombinedRestrictedScalarAux : ExactOpenCoverCombinedRestrictedScalarAux := by
  intro V TV M M0 B T X s body α Γ ctx dom cod f g arg P W syn types argument child kernel
  let a := auxiliaryTerm dom cod f arg
  let b := auxiliaryTerm dom cod g arg
  obtain ⟨childLaw⟩ := exact_OpenPackedScalarEdge X W body α Γ ctx (rawCons dom cod) f g
  obtain ⟨child⟩ := child
  obtain ⟨kernel⟩ := kernel
  have calls := Derivation.implicationElimination (Derivation.conjunctionLeft childLaw) child
  have windows := Derivation.conjunctionRight calls
  have parentLeft := exact_OpenCoverCombinedWrappedAuxFormation V TV M M0 B T s body α Γ ctx dom cod f arg
    syn types ⟨Derivation.conjunctionLeft windows⟩ argument
  have parentRight := exact_OpenCoverCombinedWrappedAuxFormation V TV M M0 B T s body α Γ ctx dom cod g arg
    syn types ⟨Derivation.conjunctionRight windows⟩ argument
  have left := exact_OpenCoverThinMatchingWindowInputs P.cover P.W P.V s body α Γ ctx cod a parentLeft
  have right := exact_OpenCoverThinMatchingWindowInputs P.cover P.W P.V s body α Γ ctx cod b parentRight
  obtain ⟨va⟩ := left.valid
  obtain ⟨vb⟩ := right.valid
  obtain ⟨wa⟩ := parentLeft
  obtain ⟨wb⟩ := parentRight
  have exchange := Derivation.implicationElimination kernel
    (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft calls) (Derivation.conjunctionIntroduction va vb))
  obtain ⟨parentLaw⟩ := exact_OpenPackedScalarEdge X W body α Γ ctx cod a b
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight parentLaw)
    (Derivation.conjunctionIntroduction exchange (Derivation.conjunctionIntroduction wa wb))⟩

#print axioms exact_OpenCoverCombinedRestrictedScalarAux
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedScalarAuxProof
