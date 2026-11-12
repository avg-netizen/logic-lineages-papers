module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineExpansionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalAlgebraProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineBinaryExpansionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalMachineState
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalRawSyntaxTransportInternalMachineStateProof OriginalRawSyntaxTransportInternalConstructorSubstitutionProof
open OriginalRawSyntaxTransportInternalMachineVisitProof OriginalStructuralNodeSizeInternalMachineBranchProof
open OriginalStructuralNodeSizeInternalMachineExpansionProof OriginalRawSyntaxTransportInternalConstructorSupportProof
open InternalApplicationResultStackCompositionStateProof (liveOfValue)
open InternalApplicationResultStackComposition (liveState)
open InternalApplicationStepPeel (graph5)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem binaryExpandOpened
    (state d k raw suffix stack codedWork out first second retFrame firstFrame secondFrame retWork secondWork firstWork : OTerm alpha)
    (hs : Nonempty (Derivation positive Delta (OpenedVisit state d k raw suffix stack codedWork)))
    (hfields : Nonempty (Derivation positive Delta (BinaryFields raw first second)))
    (hrf : Nonempty (Derivation positive Delta (graph1 finishFrame retFrame raw)))
    (hff : Nonempty (Derivation positive Delta (graph3 visitFrame firstFrame d k first)))
    (hsf : Nonempty (Derivation positive Delta (graph3 visitFrame secondFrame d k second)))
    (hrw : Nonempty (Derivation positive Delta (graph2 InternalListCodec.consCode retWork retFrame suffix)))
    (hsw : Nonempty (Derivation positive Delta (graph2 InternalListCodec.consCode secondWork secondFrame retWork)))
    (hfw : Nonempty (Derivation positive Delta (graph2 InternalListCodec.consCode firstWork firstFrame secondWork)))
    (ho : Nonempty (Derivation positive Delta (graph2 liveState out firstWork stack))) :
    Nonempty (Derivation positive Delta (graph1 (OriginalStructuralNodeSize.transition) out state)) := by
  let xs : Fin 1 → OTerm alpha := ![state]
  have inputs := openedInputs state d k raw suffix stack codedWork hs
  have hf := firstValueAt currentRaw first raw xs (inputs 2) (andLeft (andRight hfields))
  have ha := secondValueAt currentRaw second raw xs (inputs 2) (andRight (andRight hfields))
  have hfirst := visitOfValue currentType currentCutoff (firstOf currentRaw) firstFrame d k first xs hff (inputs 0) (inputs 1) hf
  have hsecond := visitOfValue currentType currentCutoff (secondOf currentRaw) secondFrame d k second xs hsf (inputs 0) (inputs 1) ha
  have hret := finishOfValue currentRaw retFrame raw xs hrf (inputs 2)
  have hretWork := binaryValue InternalListCodec.consCode (finishOf currentRaw) rest retWork retFrame suffix xs hrw hret (inputs 3)
  have hsecondWork := binaryValue InternalListCodec.consCode (visitOf currentType currentCutoff (secondOf currentRaw))
    (consOf (finishOf currentRaw) rest) secondWork secondFrame retWork xs hsw hsecond hretWork
  have hfirstWork := binaryValue InternalListCodec.consCode (visitOf currentType currentCutoff (firstOf currentRaw))
    (consOf (visitOf currentType currentCutoff (secondOf currentRaw)) (consOf (finishOf currentRaw) rest))
    firstWork firstFrame secondWork xs hfw hfirst hsecondWork
  have harity := arityValueAt currentRaw (suc (suc z)) raw xs (inputs 2) (andLeft hfields)
  apply dispatchIntro state d k raw suffix stack codedWork out hs
  apply branchNumeralIntro 2 1 (arityOf currentRaw) _ _ out xs harity
  apply branchNumeralIntro 2 2 (arityOf currentRaw) _ _ out xs harity
  exact liveOfValue _ results out firstWork stack xs ho hfirstWork (inputs 4)

theorem binaryExpand
    (state d k raw suffix stack out first second retFrame firstFrame secondFrame retWork secondWork firstWork : OTerm alpha)
    (hs : Nonempty (Derivation positive Delta (graph5 visitState state d k raw suffix stack)))
    (hfields : Nonempty (Derivation positive Delta (BinaryFields raw first second)))
    (hrf : Nonempty (Derivation positive Delta (graph1 finishFrame retFrame raw)))
    (hff : Nonempty (Derivation positive Delta (graph3 visitFrame firstFrame d k first)))
    (hsf : Nonempty (Derivation positive Delta (graph3 visitFrame secondFrame d k second)))
    (hrw : Nonempty (Derivation positive Delta (graph2 InternalListCodec.consCode retWork retFrame suffix)))
    (hsw : Nonempty (Derivation positive Delta (graph2 InternalListCodec.consCode secondWork secondFrame retWork)))
    (hfw : Nonempty (Derivation positive Delta (graph2 InternalListCodec.consCode firstWork firstFrame secondWork)))
    (ho : Nonempty (Derivation positive Delta (graph2 liveState out firstWork stack))) :
    Nonempty (Derivation positive Delta (graph1 (OriginalStructuralNodeSize.transition) out state)) := by
  apply visitCases state d k raw suffix stack _ hs
  intro beta j Theta codedWork hj hv
  rw [graph1Rename]
  have hfields' := renameInto hfields j Theta hj
  have hrf' := renameInto hrf j Theta hj
  have hff' := renameInto hff j Theta hj
  have hsf' := renameInto hsf j Theta hj
  have hrw' := renameInto hrw j Theta hj
  have hsw' := renameInto hsw j Theta hj
  have hfw' := renameInto hfw j Theta hj
  have ho' := renameInto ho j Theta hj
  rw [binaryFieldsRename] at hfields'
  rw [graph1Rename] at hrf'
  rw [graph3Rename] at hff' hsf'
  rw [graph2Rename] at hrw' hsw' hfw' ho'
  exact binaryExpandOpened (state.relabel j) (d.relabel j) (k.relabel j) (raw.relabel j)
    (suffix.relabel j) (stack.relabel j) codedWork (out.relabel j) (first.relabel j) (second.relabel j)
    (retFrame.relabel j) (firstFrame.relabel j) (secondFrame.relabel j)
    (retWork.relabel j) (secondWork.relabel j) (firstWork.relabel j)
    hv hfields' hrf' hff' hsf' hrw' hsw' hfw' ho'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineBinaryExpansionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineBinaryExpansionProof
