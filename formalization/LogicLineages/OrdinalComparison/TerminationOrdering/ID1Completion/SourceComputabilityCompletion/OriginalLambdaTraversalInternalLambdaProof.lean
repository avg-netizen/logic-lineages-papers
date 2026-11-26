module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalLambdaSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalLambdaProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalLambdaTraversal OriginalLambdaTraversalInternal
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof OriginalLambdaTraversalInternalFieldsSyntaxProof
open OriginalLambdaTraversalInternalLambdaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem lambdaBackward (leaf : Program 2)
    (value d e body parameter bodyParameter bodyOut out : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (LambdaFields value d e body parameter bodyParameter)))
    (hbody : Nonempty (Derivation positive Delta (graph2 (fold leaf) bodyOut body bodyParameter)))
    (hr : Nonempty (Derivation positive Delta (graph3 OriginalLambdaConstructor.constructor out d e bodyOut))) :
    Nonempty (Derivation positive Delta (graph2 (fold leaf) out value parameter)) := by
  apply programCases InternalUnpair.right (Fin.cons value Fin.elim0) _
  intro beta j Theta payload hj hp
  rw [graph2Rename]
  simp only [consTermRename,emptyRename] at hp
  have hf' := renameInto hf j Theta hj
  have hbody' := renameInto hbody j Theta hj
  have hr' := renameInto hr j Theta hj
  rw [lambdaFieldsRename] at hf'
  rw [graph2Rename] at hbody'
  rw [graph3Rename] at hr'
  exact atRootPayload leaf (value.relabel j) (d.relabel j) (e.relabel j) (body.relabel j)
    (parameter.relabel j) (bodyParameter.relabel j) payload (bodyOut.relabel j) (out.relabel j) hf' hp hbody' hr'

theorem lambdaForward (leaf : Program 2)
    (value d e body parameter bodyParameter bodyOut out : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (LambdaFields value d e body parameter bodyParameter)))
    (hbody : Nonempty (Derivation positive Delta (graph2 (fold leaf) bodyOut body bodyParameter)))
    (ho : Nonempty (Derivation positive Delta (graph2 (fold leaf) out value parameter))) :
    Nonempty (Derivation positive Delta (graph3 OriginalLambdaConstructor.constructor out d e bodyOut)) := by
  apply programCases OriginalLambdaConstructor.constructor (Fin.cons d (Fin.cons e (Fin.cons bodyOut Fin.elim0))) _
  intro beta j Theta produced hj hp
  rw [graph3Rename]
  simp only [consTermRename,emptyRename] at hp
  have hf' := renameInto hf j Theta hj
  have hbody' := renameInto hbody j Theta hj
  have ho' := renameInto ho j Theta hj
  rw [lambdaFieldsRename] at hf'
  rw [graph2Rename] at hbody' ho'
  have hfold := lambdaBackward leaf (value.relabel j) (d.relabel j) (e.relabel j) (body.relabel j)
    (parameter.relabel j) (bodyParameter.relabel j) (bodyOut.relabel j) produced hf' hbody' hp
  exact outputTransport OriginalLambdaConstructor.constructor produced (out.relabel j)
    (Fin.cons (d.relabel j) (Fin.cons (e.relabel j) (Fin.cons (bodyOut.relabel j) Fin.elim0)))
    (valueUnique (fold leaf) produced (out.relabel j)
      (Fin.cons (value.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) hfold ho') hp

theorem actualOriginalLambdaTraversalInternalLambda :
    OriginalLambdaTraversalInternalTargets.ActualOriginalLambdaTraversalInternalLambda := by
  intro positive leaf alpha Delta value d e body bodyOut out parameter bodyParameter
  let C := LambdaFields value d e body parameter bodyParameter ⊓
    graph2 (fold leaf) bodyOut body bodyParameter
  let G := graph2 (fold leaf) out value parameter
  let R := graph3 OriginalLambdaConstructor.constructor out d e bodyOut
  have hcG : Nonempty (Derivation positive (G :: C :: Delta) C) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hcR : Nonempty (Derivation positive (R :: C :: Delta) C) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  obtain ⟨hf⟩ := lambdaForward leaf value d e body parameter bodyParameter bodyOut out
    (andLeft hcG) (andRight hcG) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := lambdaBackward leaf value d e body parameter bodyParameter bodyOut out
    (andLeft hcR) (andRight hcR) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalLambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalLambdaProof
