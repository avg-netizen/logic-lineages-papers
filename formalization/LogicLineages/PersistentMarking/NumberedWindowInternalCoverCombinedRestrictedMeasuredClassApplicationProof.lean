module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedMeasuredClassApplicationTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedMeasuredRoundProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedMeasuredClassApplicationProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalControlGraphSupportProof (outputTransport valueUnique)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalCoverCombinedRestrictedMeasuredRoundProof
  (exact_FullyMeasuredLeastRepresentativeApplication)
open NumberedWindowInternalCoverCombinedRestrictedMeasuredClassApplicationTargets

theorem exact_FullyMeasuredClassApplication : ExactFullyMeasuredClassApplication := by
  intro V TV M M0 B T base s body α Γ ctx dom cod f g x arg m m' P W D Xm syn ty argument lf lg af ag
  have rf := exact_FullyMeasuredLeastRepresentativeApplication V TV M M0 B T base s body α Γ
    ctx dom cod f x arg m syn ty argument af lf
  have rg := exact_FullyMeasuredLeastRepresentativeApplication V TV M M0 B T base s body α Γ
    ctx dom cod g x arg m' syn ty argument ag lg
  have same := valueUnique (packedLeastProgram P.cover Xm W s) (suc m') (suc m)
    ![ctx,cod,auxiliaryTerm dom cod x arg] rg rf
  exact outputTransport (packedLeastProgram P.cover Xm W s) (suc m') (suc m)
    ![ctx,cod,auxiliaryTerm dom cod g arg] same ag

#print axioms exact_FullyMeasuredClassApplication
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedMeasuredClassApplicationProof
