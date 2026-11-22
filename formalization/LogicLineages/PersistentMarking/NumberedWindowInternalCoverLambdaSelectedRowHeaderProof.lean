module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSelectedRowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSelectedRowLiteralProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeaderFieldsOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeavesOpenDataProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSelectedRowHeaderProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel zRelabel sucRelabel)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (moveReport moveReports)
open NumberedWindowInternalSparseFieldCellSyntaxProof (moveUnary)
open NumberedWindowInternalSparseFieldCell (cellTail)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalCoverNamedLeavesOpenDataProof (namedRename)
open NumberedWindowInternalCoverLambdaSyntaxRowTargets (lambdaSyntax)
open NumberedWindowInternalCoverHeaderFieldsOpenProof (exact_OpenCoverHeaderFields)
open NumberedWindowInternalCoverLambdaSelectedRowTargets
open NumberedWindowInternalCoverLambdaSelectedRowLiteralProof (exact_OpenCoverLambdaSelectedRow)

theorem exact_OpenCoverLambdaSelectedRowAtHeader : ExactOpenCoverLambdaSelectedRowAtHeader := by
  intro V T body α Γ raw goal parent header next
  apply exact_OpenCoverHeaderFields 2 2 body α Γ raw goal header
  intro β j Δ fields keep len reports packing
  rcases fields with _ | ⟨ty,_ | ⟨q,_ | ⟨extra,rest⟩⟩⟩ <;> simp at len
  have before := moveReport j Δ keep (lambdaSyntax V T) (suc z) raw parent
  simp only [sucRelabel,zRelabel] at before
  change Nonempty (Derivation body Δ (eqn (raw.relabel j) (lambdaTerm ty q))) at packing
  have installed := moveUnary (lambdaSyntax V T) (suc z) (raw.relabel j) (lambdaTerm ty q) packing before
  apply exact_OpenCoverLambdaSelectedRow V T body β Δ ty q (goal.relabel j) installed
  intro γ k Ξ old retain evidence
  have both (p : Formula α) (hp : p ∈ Γ) : p.relabel (k ∘ j) ∈ Ξ := by
    rw [← formulaRelabelComposition j k p]
    exact retain (p.relabel j) (keep p hp)
  have reports' := moveReports k Ξ retain (raw.relabel j) cellTail [ty,q] reports
  have packing' := renameInto packing k Ξ retain
  simp only [Term.relabel_relabel,List.map_cons,List.map_nil] at reports'
  simp only [eqnRelabel,lambdaTerm,namedRename,Term.relabel_relabel] at packing'
  rw [formulaRelabelComposition j k goal]
  exact next γ (k ∘ j) Ξ (ty.relabel k) (q.relabel k) old both reports' packing' evidence

#print axioms exact_OpenCoverLambdaSelectedRowAtHeader

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSelectedRowHeaderProof
