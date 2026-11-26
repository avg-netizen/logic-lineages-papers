module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalMachineStateProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSubstitutionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalAlgebraProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineExpansionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalMachineState
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof OriginalLambdaTraversalInternalSubstitutionProof
open OriginalRawSyntaxTransportInternalMachineStateProof OriginalRawSyntaxTransportInternalConstructorSubstitutionProof
open OriginalRawSyntaxTransportInternalMachineVisitProof OriginalStructuralNodeSizeInternalMachineBranchProof
open InternalApplicationResultStackCompositionStateProof (liveOfValue)
open InternalApplicationResultStackComposition (liveState)
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Literal cutoff subtree, with inputs [cutoff, raw]. -/
def nextCutoff : Program 2 := InternalAcceptance.branch
  (sameOf (leftOf (.projection 1)) (constant 2 1)) (.projection 0) (succOf (.projection 0))

theorem cutoffSubstitution :
    Substitutes ![currentCutoff,currentRaw] nextCutoff childCutoff :=
  branchSubstitution
    (sameSubstitution (unarySubstitution InternalUnpair.left (.projection 1)) (constantSubstitution _ 1))
    (.projection 0) (unarySubstitution .succ (.projection 0))

theorem cutoffAt (state k raw next : OTerm alpha)
    (hk : Nonempty (Derivation positive Delta (graph1 currentCutoff k state)))
    (hr : Nonempty (Derivation positive Delta (graph1 currentRaw raw state)))
    (hn : Nonempty (Derivation positive Delta (graph2 nextCutoff next k raw))) :
    Nonempty (Derivation positive Delta (graph1 childCutoff next state)) :=
  (substitutionGraph cutoffSubstitution ![k,raw] ![state] next
    (fun i => Fin.cases hk (Fin.cases hr (fun a => Fin.elim0 a)) i)).mp hn

def UnaryFields (raw cutoff child childCutoff : OTerm alpha) : Formula alpha :=
  graph1 (arityOf (.projection 0)) (suc z) raw ⊓
    (graph1 (firstOf (.projection 0)) child raw ⊓ graph2 nextCutoff childCutoff cutoff raw)

def BinaryFields (raw first second : OTerm alpha) : Formula alpha :=
  graph1 (arityOf (.projection 0)) (suc (suc z)) raw ⊓
    (graph1 (firstOf (.projection 0)) first raw ⊓ graph1 (secondOf (.projection 0)) second raw)

@[simp] theorem unaryFieldsRename {beta : Type} (raw cutoff child childCutoff : OTerm alpha) (j : alpha → beta) :
    (UnaryFields raw cutoff child childCutoff).relabel j =
      UnaryFields (raw.relabel j) (cutoff.relabel j) (child.relabel j) (childCutoff.relabel j) := by
  simp only [UnaryFields,conjunctionRename,graph1Rename,graph2Rename,sucRelabel,zRelabel]

@[simp] theorem binaryFieldsRename {beta : Type} (raw first second : OTerm alpha) (j : alpha → beta) :
    (BinaryFields raw first second).relabel j = BinaryFields (raw.relabel j) (first.relabel j) (second.relabel j) := by
  simp only [BinaryFields,conjunctionRename,graph1Rename,sucRelabel,zRelabel]

theorem unaryExpandOpened
    (state d k raw suffix stack codedWork out child childK retFrame callFrame retWork callWork : OTerm alpha)
    (hs : Nonempty (Derivation positive Delta (OpenedVisit state d k raw suffix stack codedWork)))
    (hfields : Nonempty (Derivation positive Delta (UnaryFields raw k child childK)))
    (hrf : Nonempty (Derivation positive Delta (graph1 finishFrame retFrame raw)))
    (hcf : Nonempty (Derivation positive Delta (graph3 visitFrame callFrame d childK child)))
    (hrw : Nonempty (Derivation positive Delta (graph2 InternalListCodec.consCode retWork retFrame suffix)))
    (hcw : Nonempty (Derivation positive Delta (graph2 InternalListCodec.consCode callWork callFrame retWork)))
    (ho : Nonempty (Derivation positive Delta (graph2 liveState out callWork stack))) :
    Nonempty (Derivation positive Delta (graph1 (OriginalStructuralNodeSize.transition) out state)) := by
  let xs : Fin 1 → OTerm alpha := ![state]
  have inputs := openedInputs state d k raw suffix stack codedWork hs
  have hf := firstValueAt currentRaw child raw xs (inputs 2) (andLeft (andRight hfields))
  have hk := cutoffAt state k raw childK (inputs 1) (inputs 2) (andRight (andRight hfields))
  have hcall := visitOfValue currentType childCutoff (firstOf currentRaw) callFrame d childK child xs hcf (inputs 0) hk hf
  have hret := finishOfValue currentRaw retFrame raw xs hrf (inputs 2)
  have hretWork := binaryValue InternalListCodec.consCode (finishOf currentRaw) rest retWork retFrame suffix xs hrw hret (inputs 3)
  have hcallWork := binaryValue InternalListCodec.consCode (visitOf currentType childCutoff (firstOf currentRaw))
    (consOf (finishOf currentRaw) rest) callWork callFrame retWork xs hcw hcall hretWork
  apply dispatchIntro state d k raw suffix stack codedWork out hs
  apply unaryIntro state out (arityValueAt currentRaw (suc z) raw xs (inputs 2) (andLeft hfields))
  exact liveOfValue _ results out callWork stack xs ho hcallWork (inputs 4)

theorem unaryExpand
    (state d k raw suffix stack out child childK retFrame callFrame retWork callWork : OTerm alpha)
    (hs : Nonempty (Derivation positive Delta (graph5 visitState state d k raw suffix stack)))
    (hfields : Nonempty (Derivation positive Delta (UnaryFields raw k child childK)))
    (hrf : Nonempty (Derivation positive Delta (graph1 finishFrame retFrame raw)))
    (hcf : Nonempty (Derivation positive Delta (graph3 visitFrame callFrame d childK child)))
    (hrw : Nonempty (Derivation positive Delta (graph2 InternalListCodec.consCode retWork retFrame suffix)))
    (hcw : Nonempty (Derivation positive Delta (graph2 InternalListCodec.consCode callWork callFrame retWork)))
    (ho : Nonempty (Derivation positive Delta (graph2 liveState out callWork stack))) :
    Nonempty (Derivation positive Delta (graph1 (OriginalStructuralNodeSize.transition) out state)) := by
  apply visitCases state d k raw suffix stack _ hs
  intro beta j Theta codedWork hj hv
  rw [graph1Rename]
  have hfields' := renameInto hfields j Theta hj
  have hrf' := renameInto hrf j Theta hj
  have hcf' := renameInto hcf j Theta hj
  have hrw' := renameInto hrw j Theta hj
  have hcw' := renameInto hcw j Theta hj
  have ho' := renameInto ho j Theta hj
  rw [unaryFieldsRename] at hfields'
  rw [graph1Rename] at hrf'
  rw [graph3Rename] at hcf'
  rw [graph2Rename] at hrw' hcw' ho'
  exact unaryExpandOpened (state.relabel j) (d.relabel j) (k.relabel j) (raw.relabel j)
    (suffix.relabel j) (stack.relabel j) codedWork (out.relabel j) (child.relabel j) (childK.relabel j)
    (retFrame.relabel j) (callFrame.relabel j) (retWork.relabel j) (callWork.relabel j)
    hv hfields' hrf' hcf' hrw' hcw' ho'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineExpansionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineExpansionProof
