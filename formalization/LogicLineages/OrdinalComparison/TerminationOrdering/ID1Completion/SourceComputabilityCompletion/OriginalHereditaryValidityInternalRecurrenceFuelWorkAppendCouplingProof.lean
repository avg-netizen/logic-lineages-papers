module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendNodeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendCouplingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryValidity OriginalHereditaryValidityInternal
open OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendCouplingSyntaxProof
open OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendNodeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def frameHead : Program 2 := .composition InternalListCodec.headCode (fun _ : Fin 1 => .projection 0)
def frameTail : Program 2 := .composition InternalListCodec.tailCode (fun _ : Fin 1 => .projection 0)
def frameQueries : Fin 5 → Program 2 := ![frameHead,frameTail,leftOf frameHead,rightOf frameHead,
  .composition InternalApplicationValidityStackAppend.append (![frameTail,.projection 1])]

/-- The same original pair-coded head frame is reconstructed on both sides.
The suffix only changes the original remaining-work selector. -/
 theorem frameCoupling (s t m : Program 2) (front suffix joined state joinedState : OTerm alpha)
    (hnz : Nonempty (Derivation body Delta (eqn front z).not))
    (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joined front suffix)))
    (hs : Nonempty (Derivation body Delta (StateGraph state (numeral 1) front)))
    (hjs : Nonempty (Derivation body Delta (StateGraph joinedState (numeral 1) joined))) :
    Nonempty (Derivation body Delta (CoupledStep s t m state joinedState suffix)) := by
  apply queryCases frameQueries (Fin.cons front (Fin.cons suffix Fin.elim0)) _
  intro beta j ys Theta hj hq
  rw [coupledRename]
  simp only [consTermRename,emptyRename] at hq
  have hnz' := renameInto hnz j Theta hj
  rw [InternalListCodecDecompositionSupportProof.nonzeroRename] at hnz'
  have ha' := renameInto ha j Theta hj
  rw [graph2Rename] at ha'
  have hs' := renameInto hs j Theta hj
  have hjs' := renameInto hjs j Theta hj
  simp only [StateGraph,graph2Rename,oneRename] at hs' hjs'
  let xx : Fin 2 → OTerm beta := Fin.cons (front.relabel j) (Fin.cons (suffix.relabel j) Fin.elim0)
  have hh := unaryRecover InternalListCodec.headCode (.projection 0) (ys 0) (front.relabel j) xx
    (hq 0) (projectionValue 0 xx)
  have ht := unaryRecover InternalListCodec.tailCode (.projection 0) (ys 1) (front.relabel j) xx
    (hq 1) (projectionValue 0 xx)
  have hr := unaryRecover InternalUnpair.left frameHead (ys 2) (ys 0) xx (hq 2) (hq 0)
  have hp := unaryRecover InternalUnpair.right frameHead (ys 3) (ys 0) xx (hq 3) (hq 0)
  have htail := binaryRecover InternalApplicationValidityStackAppend.append frameTail (.projection 1)
    (ys 4) (ys 1) (suffix.relabel j) xx (hq 4) (hq 1) (projectionValue 1 xx)
  have hcons := InternalListCodecDecompositionSupportProof.reconstructNonzero
    (front.relabel j) (ys 0) (ys 1) hnz' hh ht
  have hjcons := InternalApplicationValidityStackAppendListProof.consForward
    (front.relabel j) (ys 0) (ys 1) (suffix.relabel j) (ys 4) (joined.relabel j) hcons htail ha'
  have hframe := reconstructPair (ys 0) (ys 2) (ys 3) hr hp
  exact nodeCoupling s t m (state.relabel j) (joinedState.relabel j) (front.relabel j) (joined.relabel j)
    (ys 0) (ys 2) (ys 3) (ys 1) (ys 4) (suffix.relabel j)
    (andIntro hs' (andIntro hcons hframe)) (andIntro hjs' (andIntro hjcons hframe)) htail

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendCouplingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendCouplingProof
