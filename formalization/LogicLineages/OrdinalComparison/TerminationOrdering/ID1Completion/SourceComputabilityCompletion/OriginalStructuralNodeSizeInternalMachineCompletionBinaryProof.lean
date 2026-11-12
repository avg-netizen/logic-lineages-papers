module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionIntroductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineBinaryStatesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineIterationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalAlgebraProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionBinaryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalMachineState
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalAdditionLawsProof (add)
open InternalOriginalOrderSyntaxProof (addRelabel)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalStructuralNodeSizeInternalMachineExpansionProof
open OriginalStructuralNodeSizeInternalMachineCompletion OriginalStructuralNodeSizeInternalMachineCompletionSyntaxProof
open OriginalStructuralNodeSizeInternalMachineCompletionBindingProof OriginalStructuralNodeSizeInternalMachineCompletionIntroductionProof
open OriginalStructuralNodeSizeInternalMachineIterationProof
open InternalApplicationStepPeel (graph5)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem binaryRun
    (d k raw first second cf ca firstOut secondOut produced work stack start finish : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (BinaryFields raw first second)))
    (hp : Nonempty (Derivation positive Delta (graph3 (OriginalStructuralNodeSizeInternalAlgebraProof.rebuild) produced raw firstOut secondOut)))
    (hcf : Nonempty (Derivation positive Delta (Completes d k first cf firstOut)))
    (hca : Nonempty (Derivation positive Delta (Completes d k second ca secondOut)))
    (hi : Nonempty (Derivation positive Delta (graph5 visitState start d k raw work stack)))
    (ho : Nonempty (Derivation positive Delta (graph3 returnState finish produced work stack))) :
    Nonempty (Derivation positive Delta
      (graph2 (OriginalStructuralNodeSize.iterate) finish (suc (add cf (add ca (suc z)))) start)) := by
  apply OriginalStructuralNodeSizeInternalMachineBinaryStatesProof.cases start finish d k raw first second
    firstOut secondOut produced work stack _ hf hp hi ho
  intro beta j Theta workRet workSecond resultFirst s1 s2 s3 hj hs
  simp only [graph2Rename,sucRelabel,addRelabel,zRelabel]
  have hcf' := renameInto hcf j Theta hj
  have hca' := renameInto hca j Theta hj
  rw [completesRename] at hcf' hca'
  have h1 := andLeft hs
  have hfVisit := andLeft (andRight hs)
  have hfReturn := andLeft (andRight (andRight hs))
  have haVisit := andLeft (andRight (andRight (andRight hs)))
  have haReturn := andLeft (andRight (andRight (andRight (andRight hs))))
  have hlast := andRight (andRight (andRight (andRight (andRight hs))))
  have rf := completesApply (d.relabel j) (k.relabel j) (first.relabel j) (cf.relabel j) (firstOut.relabel j)
    workSecond (stack.relabel j) s1 s2 hcf' hfVisit hfReturn
  have ra := completesApply (d.relabel j) (k.relabel j) (second.relabel j) (ca.relabel j) (secondOut.relabel j)
    workRet resultFirst s2 s3 hca' haVisit haReturn
  exact iterateAfterFirst (add (cf.relabel j) (add (ca.relabel j) (suc z)))
    (start.relabel j) s1 (finish.relabel j) h1
    (iterateCompose (cf.relabel j) (add (ca.relabel j) (suc z)) s1 s2 (finish.relabel j) rf
      (iterateCompose (ca.relabel j) (suc z) s2 s3 (finish.relabel j) ra
        (iterateOne s3 (finish.relabel j) hlast)))

theorem binaryComplete
    (d k raw first second cf ca firstOut secondOut produced : OTerm alpha)
    (hf : Nonempty (Derivation positive Delta (BinaryFields raw first second)))
    (hp : Nonempty (Derivation positive Delta (graph3 (OriginalStructuralNodeSizeInternalAlgebraProof.rebuild) produced raw firstOut secondOut)))
    (hcf : Nonempty (Derivation positive Delta (Completes d k first cf firstOut)))
    (hca : Nonempty (Derivation positive Delta (Completes d k second ca secondOut))) :
    Nonempty (Derivation positive Delta
      (Completes d k raw (suc (add cf (add ca (suc z)))) produced)) := by
  apply completesByRuns
  intro beta j Theta work stack start finish hj hi ho
  simp only [sucRelabel,addRelabel,zRelabel]
  have hf' := renameInto hf j Theta hj
  have hp' := renameInto hp j Theta hj
  have hcf' := renameInto hcf j Theta hj
  have hca' := renameInto hca j Theta hj
  rw [binaryFieldsRename] at hf'
  rw [graph3Rename] at hp'
  rw [completesRename] at hcf' hca'
  exact binaryRun (d.relabel j) (k.relabel j) (raw.relabel j) (first.relabel j) (second.relabel j)
    (cf.relabel j) (ca.relabel j) (firstOut.relabel j) (secondOut.relabel j)
    (produced.relabel j) work stack start finish hf' hp' hcf' hca' hi ho

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionBinaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineCompletionBinaryProof
