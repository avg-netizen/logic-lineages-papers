module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionTotalityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionRunProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalRunShapeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalLambdaTraversal OriginalLambdaTraversalInternal
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalDerivationRenamingSyntaxProof (existsRename)
open OriginalLambdaTraversalInternalCompletionBindingProof OriginalLambdaTraversalInternalCompletionTotalityProof
open OriginalLambdaTraversalInternalCompletionRunProof OriginalLambdaTraversalInternalRunStateProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

@[simp] theorem finishedRunRename {beta : Type} (state : OTerm alpha) (j : alpha → beta) :
    (FinishedRun state).relabel j = FinishedRun (state.relabel j) := by
  simp only [FinishedRun,existsRename,graph1Rename,Term.relabel,Term.relabel_relabel] <;> rfl

theorem runShapeAtPayload (leaf : Program 2) (state value parameter payload : OTerm alpha)
    (hp : Nonempty (Derivation positive Delta (graph1 InternalUnpair.right payload value)))
    (hr : Nonempty (Derivation positive Delta (graph2 (run leaf) state value parameter))) :
    Nonempty (Derivation positive Delta (FinishedRun state)) := by
  apply hasCompletionCases leaf value parameter payload _ (hasCompletion leaf value parameter payload hp)
  intro beta j Theta count produced hj hb hc
  rw [finishedRunRename]
  have hp' := renameInto hp j Theta hj
  have hr' := renameInto hr j Theta hj
  rw [graph1Rename] at hp'
  rw [graph2Rename] at hr'
  exact finishedRunIntro (state.relabel j) produced
    (completionRun leaf (value.relabel j) (parameter.relabel j) (payload.relabel j) count produced
      (state.relabel j) hp' hb hc hr')

theorem runShape (leaf : Program 2) (state value parameter : OTerm alpha)
    (hr : Nonempty (Derivation positive Delta (graph2 (run leaf) state value parameter))) :
    Nonempty (Derivation positive Delta (FinishedRun state)) := by
  apply programCases InternalUnpair.right (Fin.cons value Fin.elim0) _
  intro beta j Theta payload hj hp
  rw [finishedRunRename]
  simp only [consTermRename,emptyRename] at hp
  have hr' := renameInto hr j Theta hj
  rw [graph2Rename] at hr'
  exact runShapeAtPayload leaf (state.relabel j) (value.relabel j) (parameter.relabel j) payload hp hr'

theorem actualOriginalLambdaTraversalInternalRunShape :
    OriginalLambdaTraversalInternalTargets.ActualOriginalLambdaTraversalInternalRunShape := by
  intro positive leaf alpha Delta state value parameter
  obtain ⟨h⟩ := runShape (positive := positive)
    (Delta := graph2 (run leaf) state value parameter :: Delta) leaf state value parameter
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalRunShapeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalRunShapeProof
