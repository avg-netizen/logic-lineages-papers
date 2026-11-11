module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionIntroductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionRunProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionOutputProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalLambdaTraversal OriginalLambdaTraversalInternal
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn eqnRelabel)
open InternalTagArithmeticSupportProof (symm)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalLambdaTraversalInternalCompletion OriginalLambdaTraversalInternalCompletionSyntaxProof
open OriginalLambdaTraversalInternalCompletionBindingProof OriginalLambdaTraversalInternalCompletionIntroductionProof
open OriginalLambdaTraversalInternalCompletionRunProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem producedTransport (leaf : Program 2) (value parameter count first second : OTerm alpha)
    (he : Nonempty (Derivation positive Delta (eqn first second)))
    (hc : Nonempty (Derivation positive Delta (Completes leaf value parameter count first))) :
    Nonempty (Derivation positive Delta (Completes leaf value parameter count second)) := by
  apply completesByRuns
  intro beta j Theta work stack start finish hj hi ho
  have he' := renameInto he j Theta hj
  rw [eqnRelabel] at he'
  obtain ⟨he'⟩ := he'
  have hc' := renameInto hc j Theta hj
  rw [completesRename] at hc'
  exact completesApply leaf (value.relabel j) (parameter.relabel j) (count.relabel j) (first.relabel j)
    work stack start finish hc' hi
    (headTransport returnState finish (second.relabel j) (first.relabel j)
      (Fin.cons work (Fin.cons stack Fin.elim0)) ⟨symm he'⟩ ho)

theorem completionAtFoldCases (leaf : Program 2)
    (value parameter payload produced : OTerm alpha) (psi : Formula alpha)
    (hp : Nonempty (Derivation positive Delta (graph1 InternalUnpair.right payload value)))
    (ho : Nonempty (Derivation positive Delta (graph2 (fold leaf) produced value parameter)))
    (hc : Nonempty (Derivation positive Delta (HasCompletion leaf value parameter payload)))
    (k : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (count : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation positive Theta
        (InternalPairingSumBounds.weakBound count (payloadFuel (payload.relabel j)))) →
      Nonempty (Derivation positive Theta
        (Completes leaf (value.relabel j) (parameter.relabel j) count (produced.relabel j))) →
      Nonempty (Derivation positive Theta (psi.relabel j))) : Nonempty (Derivation positive Delta psi) := by
  apply hasCompletionCases leaf value parameter payload psi hc
  intro beta j Theta count actual hj hb hd
  have hp' := renameInto hp j Theta hj
  have ho' := renameInto ho j Theta hj
  rw [graph1Rename] at hp'
  rw [graph2Rename] at ho'
  have hactual := completionFold leaf (value.relabel j) (parameter.relabel j) (payload.relabel j)
    count actual hp' hb hd
  have he := valueUnique (fold leaf) actual (produced.relabel j)
    (Fin.cons (value.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) hactual ho'
  exact k beta j Theta count hj hb
    (producedTransport leaf (value.relabel j) (parameter.relabel j) count actual (produced.relabel j) he hd)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionOutputProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionOutputProof
