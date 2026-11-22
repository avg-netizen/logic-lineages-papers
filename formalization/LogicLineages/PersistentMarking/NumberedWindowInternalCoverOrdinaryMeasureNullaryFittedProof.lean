module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverOrdinaryMeasureTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverOrdinaryMeasureNullaryPairProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeadWindowSelectedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNullaryScratchProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverOrdinaryMeasureNullaryFittedProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalTagArithmeticSyntaxProof (z)
open NumberedWindowInternalCoverRefinedInductionDispatchTargets (ParentRow)
open NumberedWindowInternalCoverHeadWindowSelectedProof (exact_OpenCoverHeadFittedWindow)
open NumberedWindowInternalCoverOrdinaryMeasureNullaryPairProof (exact_OpenCoverOrdinaryNullaryPair)
open NumberedWindowInternalCoverSelectedGrammarNullaryScratchProof (exact_OpenSelectedGrammarNullaryScratch)
open NumberedWindowInternalCoverOrdinaryMeasureTargets

theorem exact_OpenCoverOrdinaryNullaryFitted : ExactOpenCoverOrdinaryNullaryFitted := by
  intro V TV M A B T s body α Γ h p vertices ctx result row
  have head := exact_OpenCoverHeadFittedWindow false s B T body α Γ ctx h result [z] rfl row.typed
  have pair := exact_OpenCoverOrdinaryNullaryPair M A body α Γ h p row.parent.measured
  exact exact_OpenSelectedGrammarNullaryScratch (ordinaryPrograms s V TV M A B T).V
    (ordinarySharedMeasure M A) s body α Γ p z z vertices h
    head row.parent.valid row.parent.measured pair row.parent.held

#print axioms exact_OpenCoverOrdinaryNullaryFitted

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverOrdinaryMeasureNullaryFittedProof
