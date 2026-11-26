module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionIntroductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineUnaryStatesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineIterationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalAlgebraProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionUnaryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalMachineState
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalStructuralNodeSizeInternalMachineExpansionProof
open OriginalStructuralNodeSizeInternalMachineCompletion OriginalStructuralNodeSizeInternalMachineCompletionSyntaxProof
open OriginalStructuralNodeSizeInternalMachineCompletionBindingProof OriginalStructuralNodeSizeInternalMachineCompletionIntroductionProof
open OriginalStructuralNodeSizeInternalMachineIterationProof
open InternalApplicationStepPeel (graph5)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem unaryRun
    (d k raw child childK count childOut produced work stack start finish : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (UnaryFields raw k child childK)))
    (hp : Nonempty (Derivation positive Delta (graph3 (OriginalStructuralNodeSizeInternalAlgebraProof.rebuild) produced raw childOut z)))
    (hc : Nonempty (Derivation positive Delta (Completes d childK child count childOut)))
    (hi : Nonempty (Derivation positive Delta (graph5 visitState start d k raw work stack)))
    (ho : Nonempty (Derivation positive Delta (graph3 returnState finish produced work stack))) :
    Nonempty (Derivation positive Delta (graph2 (OriginalStructuralNodeSize.iterate) finish (suc (suc count)) start)) := by
  apply OriginalStructuralNodeSizeInternalMachineUnaryStatesProof.cases start finish d k raw child childK
    childOut produced work stack _ hf hp hi ho
  intro beta j Theta workRet s1 s2 hj hs
  simp only [graph2Rename,sucRelabel]
  have hc' := renameInto hc j Theta hj
  rw [completesRename] at hc'
  have hr := completesApply (d.relabel j) (childK.relabel j) (child.relabel j) (count.relabel j)
    (childOut.relabel j) workRet (stack.relabel j) s1 s2 hc'
    (andLeft (andRight hs)) (andLeft (andRight (andRight hs)))
  exact iterateAfterFirst (suc (count.relabel j)) (start.relabel j) s1 (finish.relabel j) (andLeft hs)
    (iterateAfterLast (count.relabel j) s1 s2 (finish.relabel j) hr (andRight (andRight (andRight hs))))

theorem unaryComplete
    (d k raw child childK count childOut produced : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (UnaryFields raw k child childK)))
    (hp : Nonempty (Derivation positive Delta (graph3 (OriginalStructuralNodeSizeInternalAlgebraProof.rebuild) produced raw childOut z)))
    (hc : Nonempty (Derivation positive Delta (Completes d childK child count childOut))) :
    Nonempty (Derivation positive Delta (Completes d k raw (suc (suc count)) produced)) := by
  apply completesByRuns
  intro beta j Theta work stack start finish hj hi ho
  simp only [sucRelabel]
  have hf' := renameInto hf j Theta hj
  have hp' := renameInto hp j Theta hj
  have hc' := renameInto hc j Theta hj
  rw [unaryFieldsRename] at hf'
  simp only [graph3Rename,zRelabel] at hp'
  rw [completesRename] at hc'
  exact unaryRun (d.relabel j) (k.relabel j) (raw.relabel j) (child.relabel j) (childK.relabel j)
    (count.relabel j) (childOut.relabel j) (produced.relabel j) work stack start finish hf' hp' hc' hi ho

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionUnaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionUnaryProof
