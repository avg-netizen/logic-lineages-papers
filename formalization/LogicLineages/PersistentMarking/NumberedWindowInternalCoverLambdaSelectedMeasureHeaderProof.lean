module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSelectedMeasureTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSelectedMeasureChildProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverHeaderFieldsOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverNamedLeavesOpenDataProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSelectedMeasureHeaderProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (moveReport moveReports)
open NumberedWindowInternalSparseFieldCellSyntaxProof (moveUnary)
open NumberedWindowInternalSparseFieldCell (cellTail)
open NumberedWindowInternalCoverLambdaLayerTargets (lambdaTerm)
open NumberedWindowInternalCoverNamedLeavesOpenDataProof (namedRename)
open NumberedWindowInternalCoverLambdaMeasureRowTargets (lambdaMeasure)
open NumberedWindowInternalCoverHeaderFieldsOpenProof (exact_OpenCoverHeaderFields)
open NumberedWindowInternalCoverLambdaSelectedMeasureTargets
open NumberedWindowInternalCoverLambdaSelectedMeasureChildProof (exact_OpenCoverLambdaSelectedMeasure)

theorem exact_OpenCoverLambdaSelectedMeasureAtHeader : ExactOpenCoverLambdaSelectedMeasureAtHeader := by
  intro M body α Γ raw p goal parent header next
  apply exact_OpenCoverHeaderFields 2 2 body α Γ raw goal header
  intro β j Δ fields keep len reports packing
  rcases fields with _ | ⟨ty,_ | ⟨q,_ | ⟨extra,rest⟩⟩⟩ <;> simp at len
  have before := moveReport j Δ keep (lambdaMeasure M) p raw parent
  change Nonempty (Derivation body Δ (eqn (raw.relabel j) (lambdaTerm ty q))) at packing
  have installed := moveUnary (lambdaMeasure M) (p.relabel j) (raw.relabel j) (lambdaTerm ty q) packing before
  apply exact_OpenCoverLambdaSelectedMeasure M body β Δ ty q (p.relabel j) (goal.relabel j) installed
  intro γ k Ξ old mc d w retain evidence
  have both (p : Formula α) (hp : p ∈ Γ) : p.relabel (k ∘ j) ∈ Ξ := by
    rw [← formulaRelabelComposition j k p]
    exact retain (p.relabel j) (keep p hp)
  have reports' := moveReports k Ξ retain (raw.relabel j) cellTail [ty,q] reports
  have packing' := renameInto packing k Ξ retain
  simp only [Term.relabel_relabel,List.map_cons,List.map_nil] at reports'
  simp only [eqnRelabel,lambdaTerm,namedRename,Term.relabel_relabel] at packing'
  simp only [Term.relabel_relabel] at evidence
  rw [formulaRelabelComposition j k goal]
  exact next γ (k ∘ j) Ξ (ty.relabel k) (q.relabel k) old mc d w both reports' packing' evidence

#print axioms exact_OpenCoverLambdaSelectedMeasureAtHeader

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaSelectedMeasureHeaderProof
