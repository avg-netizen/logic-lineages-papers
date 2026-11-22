module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedDirectedXTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedDirectedXLiftProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedScalarAuxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedDirectedXProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus
open NumberedWindowInternalCoverCombinedRestrictedScalarAuxTargets (localAuxExchange)
open NumberedWindowInternalCoverCombinedRestrictedScalarAuxProof (exact_OpenCoverCombinedRestrictedScalarAux)
open NumberedWindowInternalCoverCombinedRestrictedDirectedXLiftProof (exact_OpenAuxMemoFunctionLift)
open NumberedWindowInternalCoverCombinedRestrictedDirectedXTargets

theorem exact_OpenCoverCombinedRestrictedDirectedX : ExactOpenCoverCombinedRestrictedDirectedX := by
  intro V TV M M0 B T base s body α Γ ctx dom cod f g arg P W X syn types argument child
  have kernel : Nonempty (Derivation body Γ (localAuxExchange X P.V dom cod f g arg)) :=
    exact_OpenAuxMemoFunctionLift base P.V body α Γ dom cod f g arg
  exact exact_OpenCoverCombinedRestrictedScalarAux V TV M M0 B T X s body α Γ ctx dom cod f g arg
    syn types argument child kernel

#print axioms exact_OpenCoverCombinedRestrictedDirectedX
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedDirectedXProof
