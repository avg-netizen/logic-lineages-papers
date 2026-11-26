module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionRunProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalLambdaTraversal OriginalLambdaTraversalInternal
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalLambdaTraversalInternalCompletionLeafProof OriginalLambdaTraversalInternalCompletionRunProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem leafBackward (leaf : Program 2) (value out parameter : OTerm alpha)
    (ht : Nonempty (Derivation positive Delta (graph1 otherTag (suc z) value)))
    (ho : Nonempty (Derivation positive Delta (graph2 leaf out value parameter))) :
    Nonempty (Derivation positive Delta (graph2 (fold leaf) out value parameter)) := by
  apply programCases InternalUnpair.right (Fin.cons value Fin.elim0) _
  intro beta j Theta payload hj hp
  rw [graph2Rename]
  simp only [consTermRename,emptyRename] at hp
  have ht' := renameInto ht j Theta hj
  have ho' := renameInto ho j Theta hj
  simp only [graph1Rename,graph2Rename,sucRelabel,zRelabel] at ht' ho'
  exact completionFold leaf (value.relabel j) (parameter.relabel j) payload (suc z) (out.relabel j)
    hp (leafBound payload) (leafComplete leaf (value.relabel j) (parameter.relabel j) (out.relabel j) ht' ho')

theorem leafForward (leaf : Program 2) (value out parameter : OTerm alpha)
    (ht : Nonempty (Derivation positive Delta (graph1 otherTag (suc z) value)))
    (ho : Nonempty (Derivation positive Delta (graph2 (fold leaf) out value parameter))) :
    Nonempty (Derivation positive Delta (graph2 leaf out value parameter)) := by
  apply programCases leaf (Fin.cons value (Fin.cons parameter Fin.elim0)) _
  intro beta j Theta produced hj hp
  rw [graph2Rename]
  simp only [consTermRename,emptyRename] at hp
  have ht' := renameInto ht j Theta hj
  have ho' := renameInto ho j Theta hj
  simp only [graph1Rename,graph2Rename,sucRelabel,zRelabel] at ht' ho'
  have hf := leafBackward leaf (value.relabel j) produced (parameter.relabel j) ht' hp
  exact outputTransport leaf produced (out.relabel j)
    (Fin.cons (value.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))
    (valueUnique (fold leaf) produced (out.relabel j)
      (Fin.cons (value.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) hf ho') hp

theorem actualOriginalLambdaTraversalInternalLeaf :
    OriginalLambdaTraversalInternalTargets.ActualOriginalLambdaTraversalInternalLeaf := by
  intro positive leaf alpha Delta value out parameter
  let C := graph1 otherTag (suc z) value
  let G := graph2 (fold leaf) out value parameter
  let R := graph2 leaf out value parameter
  have hcG : Nonempty (Derivation positive (G :: C :: Delta) C) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hcR : Nonempty (Derivation positive (R :: C :: Delta) C) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  obtain ⟨hf⟩ := leafForward leaf value out parameter hcG ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := leafBackward leaf value out parameter hcR ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalLeafProof
