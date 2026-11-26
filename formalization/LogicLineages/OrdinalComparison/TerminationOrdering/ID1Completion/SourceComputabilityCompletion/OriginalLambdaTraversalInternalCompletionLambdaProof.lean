module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionIntroductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalConstructorLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalIterationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionLambdaProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalLambdaTraversal OriginalLambdaTraversalInternal
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalLambdaTraversalInternalCompletion OriginalLambdaTraversalInternalCompletionSyntaxProof
open OriginalLambdaTraversalInternalCompletionBindingProof OriginalLambdaTraversalInternalCompletionIntroductionProof
open OriginalLambdaTraversalInternalIterationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem lambdaRun (leaf : Program 2)
    (value d e body parameter bodyParameter cb bodyOut produced work stack start finish : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (LambdaFields value d e body parameter bodyParameter)))
    (hp : Nonempty (Derivation positive Delta (graph3 OriginalLambdaConstructor.constructor produced d e bodyOut)))
    (hcb : Nonempty (Derivation positive Delta (Completes leaf body bodyParameter cb bodyOut)))
    (hi : Nonempty (Derivation positive Delta (graph4 visitState start value parameter work stack)))
    (ho : Nonempty (Derivation positive Delta (graph3 returnState finish produced work stack))) :
    Nonempty (Derivation positive Delta (graph2 (iterate leaf) finish (suc (suc cb)) start)) := by
  apply OriginalLambdaTraversalInternalConstructorLambdaProof.cases leaf start finish value produced d e body
    parameter bodyParameter work stack bodyOut _ hf hp hi ho
  intro beta j Theta workRet s1 s2 hj hs
  simp only [graph2Rename,sucRelabel]
  have hcb' := renameInto hcb j Theta hj
  rw [completesRename] at hcb'
  have hr := completesApply leaf (body.relabel j) (bodyParameter.relabel j) (cb.relabel j) (bodyOut.relabel j)
    workRet (stack.relabel j) s1 s2 hcb' (andLeft (andRight hs)) (andLeft (andRight (andRight hs)))
  exact iterateAfterFirst leaf (suc (cb.relabel j)) (start.relabel j) s1 (finish.relabel j) (andLeft hs)
    (iterateAfterLast leaf (cb.relabel j) s1 s2 (finish.relabel j) hr (andRight (andRight (andRight hs))))

theorem lambdaComplete (leaf : Program 2)
    (value d e body parameter bodyParameter cb bodyOut produced : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (LambdaFields value d e body parameter bodyParameter)))
    (hp : Nonempty (Derivation positive Delta (graph3 OriginalLambdaConstructor.constructor produced d e bodyOut)))
    (hcb : Nonempty (Derivation positive Delta (Completes leaf body bodyParameter cb bodyOut))) :
    Nonempty (Derivation positive Delta (Completes leaf value parameter (suc (suc cb)) produced)) := by
  apply completesByRuns
  intro beta j Theta work stack start finish hj hi ho
  simp only [sucRelabel]
  have hf' := renameInto hf j Theta hj
  have hp' := renameInto hp j Theta hj
  have hcb' := renameInto hcb j Theta hj
  simp only [LambdaFields,conjunctionRename,graph1Rename,graph2Rename,
    InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hf'
  rw [graph3Rename] at hp'
  rw [completesRename] at hcb'
  exact lambdaRun leaf (value.relabel j) (d.relabel j) (e.relabel j) (body.relabel j)
    (parameter.relabel j) (bodyParameter.relabel j) (cb.relabel j) (bodyOut.relabel j)
    (produced.relabel j) work stack start finish hf' hp' hcb' hi ho

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionLambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionLambdaProof
