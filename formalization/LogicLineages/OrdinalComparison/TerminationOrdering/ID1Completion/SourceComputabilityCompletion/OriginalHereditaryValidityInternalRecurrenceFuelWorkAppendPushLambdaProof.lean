module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendPushProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalPushSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendPushLambdaProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryValidityInternal OriginalHereditaryValidityInternalPushSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def lambdaFrame : Program 4 := pairOf (.projection 0) (.projection 1)
def lambdaFrontWork : Program 4 := consOf lambdaFrame (.projection 2)
def lambdaJoinedWork : Program 4 := consOf lambdaFrame (.projection 3)
def lambdaPushQueries : Fin 5 → Program 4 := ![lambdaFrame,lambdaFrontWork,lambdaJoinedWork,
  pairOf (InternalLessThan.constantOne 4) lambdaFrontWork,
  pairOf (InternalLessThan.constantOne 4) lambdaJoinedWork]

 theorem lambdaPushCases (child parameter frontRest joinedRest suffix : OTerm alpha) (psi : Formula alpha)
    (ha : Nonempty (Derivation body Delta
      (graph2 InternalApplicationValidityStackAppend.append joinedRest frontRest suffix)))
    (k : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (frontWork joinedWork frontState joinedState : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta
        (graph2 InternalApplicationValidityStackAppend.append joinedWork frontWork (suffix.relabel j))) →
      Nonempty (Derivation body Theta (StateGraph frontState (numeral 1) frontWork)) →
      Nonempty (Derivation body Theta (StateGraph joinedState (numeral 1) joinedWork)) →
      Nonempty (Derivation body Theta (PushedFrame frontState (child.relabel j)
        (parameter.relabel j) (frontRest.relabel j))) →
      Nonempty (Derivation body Theta (PushedFrame joinedState (child.relabel j)
        (parameter.relabel j) (joinedRest.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
  let xs : Fin 4 → OTerm alpha := Fin.cons child
    (Fin.cons parameter (Fin.cons frontRest (Fin.cons joinedRest Fin.elim0)))
  apply queryCases lambdaPushQueries xs psi
  intro beta j ys Theta hj hq
  simp only [xs,consTermRename,emptyRename] at hq
  have ha' := renameInto ha j Theta hj
  rw [graph2Rename] at ha'
  let xx : Fin 4 → OTerm beta := Fin.cons (child.relabel j)
    (Fin.cons (parameter.relabel j) (Fin.cons (frontRest.relabel j) (Fin.cons (joinedRest.relabel j) Fin.elim0)))
  have hframe := binaryRecover InternalPairing.pairing (.projection 0) (.projection 1)
    (ys 0) (child.relabel j) (parameter.relabel j) xx (hq 0) (projectionValue 0 xx) (projectionValue 1 xx)
  have hfw := binaryRecover InternalListCodec.consCode lambdaFrame (.projection 2)
    (ys 1) (ys 0) (frontRest.relabel j) xx (hq 1) (hq 0) (projectionValue 2 xx)
  have hjw := binaryRecover InternalListCodec.consCode lambdaFrame (.projection 3)
    (ys 2) (ys 0) (joinedRest.relabel j) xx (hq 2) (hq 0) (projectionValue 3 xx)
  have hfs := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 4) lambdaFrontWork
    (ys 3) (numeral 1) (ys 1) xx (hq 3) (InternalLessThanSupportProof.oneConstantValue xx) (hq 1)
  have hjs := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 4) lambdaJoinedWork
    (ys 4) (numeral 1) (ys 2) xx (hq 4) (InternalLessThanSupportProof.oneConstantValue xx) (hq 2)
  have haWork := InternalApplicationValidityStackAppendListProof.consBackward
    (ys 1) (ys 0) (frontRest.relabel j) (suffix.relabel j) (joinedRest.relabel j) (ys 2) hfw ha' hjw
  exact k beta j Theta (ys 1) (ys 2) (ys 3) (ys 4) hj haWork hfs hjs
    (pushedFrameIntro (ys 3) (child.relabel j) (parameter.relabel j) (frontRest.relabel j)
      (ys 1) (ys 0) (andIntro hfs (andIntro hfw hframe)))
    (pushedFrameIntro (ys 4) (child.relabel j) (parameter.relabel j) (joinedRest.relabel j)
      (ys 2) (ys 0) (andIntro hjs (andIntro hjw hframe)))

 theorem statePairCases (front joined : OTerm alpha) (psi : Formula alpha)
    (k : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (state joinedState : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (StateGraph state (numeral 1) (front.relabel j))) →
      Nonempty (Derivation body Theta (StateGraph joinedState (numeral 1) (joined.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
  let qs : Fin 2 → Program 2 := ![pairOf (InternalLessThan.constantOne 2) (.projection 0),
    pairOf (InternalLessThan.constantOne 2) (.projection 1)]
  apply queryCases qs (Fin.cons front (Fin.cons joined Fin.elim0)) psi
  intro beta j ys Theta hj hq
  simp only [consTermRename,emptyRename] at hq
  let xx : Fin 2 → OTerm beta := Fin.cons (front.relabel j) (Fin.cons (joined.relabel j) Fin.elim0)
  exact k beta j Theta (ys 0) (ys 1) hj
    (binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 2) (.projection 0)
      (ys 0) (numeral 1) (front.relabel j) xx (hq 0)
      (InternalLessThanSupportProof.oneConstantValue xx) (projectionValue 0 xx))
    (binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 2) (.projection 1)
      (ys 1) (numeral 1) (joined.relabel j) xx (hq 1)
      (InternalLessThanSupportProof.oneConstantValue xx) (projectionValue 1 xx))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendPushLambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendPushLambdaProof
