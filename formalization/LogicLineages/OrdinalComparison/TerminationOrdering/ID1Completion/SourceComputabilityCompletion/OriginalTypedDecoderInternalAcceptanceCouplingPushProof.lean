module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendPushLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalPushProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingPushProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderInternalScalarSyntaxProof OriginalTypedDecoderInternalPushSyntaxProof
open OriginalTypedDecoderInternalRequestSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Construct both actual live states, keeping the literal work unchanged. -/
theorem pushZeroCases (front joined suffix : OTerm alpha) (psi : Formula alpha)
    (ha : Nonempty (Derivation body Delta
      (graph2 InternalApplicationValidityStackAppend.append joined front suffix)))
    (k : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (frontState joinedState : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta
        (graph2 InternalApplicationValidityStackAppend.append (joined.relabel j) (front.relabel j) (suffix.relabel j))) →
      Nonempty (Derivation body Theta (StepLive frontState (front.relabel j))) →
      Nonempty (Derivation body Theta (StepLive joinedState (joined.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
  apply OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendPushLambdaProof.statePairCases front joined psi
  intro beta j Theta fs js hj hfs hjs
  have ha' := renameInto ha j Theta hj
  rw [graph2Rename] at ha'
  exact k beta j Theta fs js hj ha' hfs hjs

def oneRequest : Program 6 := pairOf (.projection 0) (pairOf (.projection 1) (pairOf (.projection 2) (.projection 3)))
def oneFront : Program 6 := consOf oneRequest (.projection 4)
def oneJoined : Program 6 := consOf oneRequest (.projection 5)
def oneQueries : Fin 5 → Program 6 := ![oneRequest,oneFront,oneJoined,pairOf (InternalLessThan.constantOne 6) oneFront,pairOf (InternalLessThan.constantOne 6) oneJoined]

theorem pushOneCases (mode gamma typ raw front joined suffix : OTerm alpha) (psi : Formula alpha)
    (ha : Nonempty (Derivation body Delta
      (graph2 InternalApplicationValidityStackAppend.append joined front suffix)))
    (k : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (frontWork joinedWork frontState joinedState : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta
        (graph2 InternalApplicationValidityStackAppend.append joinedWork frontWork (suffix.relabel j))) →
      Nonempty (Derivation body Theta (StepLive frontState frontWork)) →
      Nonempty (Derivation body Theta (StepLive joinedState joinedWork)) →
      Nonempty (Derivation body Theta (StepPushOne frontState (mode.relabel j) (gamma.relabel j) (typ.relabel j) (raw.relabel j) (front.relabel j))) →
      Nonempty (Derivation body Theta (StepPushOne joinedState (mode.relabel j) (gamma.relabel j) (typ.relabel j) (raw.relabel j) (joined.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
  let xs : Fin 6 → OTerm alpha := ![mode,gamma,typ,raw,front,joined]
  apply queryCases oneQueries xs psi
  intro beta j ys Theta hj hq
  have ha' := renameInto ha j Theta hj
  rw [graph2Rename] at ha'
  let xx : Fin 6 → OTerm beta := fun i => (xs i).relabel j
  have hr0 := OriginalTypedDecoderInternalRequestProof.requestForward
    (.projection 0) (.projection 1) (.projection 2) (.projection 3)
    (ys 0) (mode.relabel j) (gamma.relabel j) (typ.relabel j) (raw.relabel j) xx
    (projectionValue 0 xx) (projectionValue 1 xx)
    (projectionValue 2 xx) (projectionValue 3 xx) (hq 0)
  have hfw := binaryRecover InternalListCodec.consCode oneRequest (.projection 4)
    (ys 1) (ys 0) (front.relabel j) xx (hq 1) (hq 0) (projectionValue 4 xx)
  have hjw := binaryRecover InternalListCodec.consCode oneRequest (.projection 5)
    (ys 2) (ys 0) (joined.relabel j) xx (hq 2) (hq 0) (projectionValue 5 xx)
  have happ := InternalApplicationValidityStackAppendListProof.consBackward
    (ys 1) (ys 0) (front.relabel j) (suffix.relabel j) (joined.relabel j) (ys 2) hfw ha' hjw
  have hfs := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 6) oneFront
    (ys 3) (numeral 1) (ys 1) xx (hq 3) (InternalLessThanSupportProof.oneConstantValue xx) (hq 1)
  have hjs := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 6) oneJoined
    (ys 4) (numeral 1) (ys 2) xx (hq 4) (InternalLessThanSupportProof.oneConstantValue xx) (hq 2)
  exact k beta j Theta (ys 1) (ys 2) (ys 3) (ys 4) hj happ hfs hjs
    (stepPushOneIntro (ys 3) (mode.relabel j) (gamma.relabel j) (typ.relabel j) (raw.relabel j) (front.relabel j) ![ys 0,ys 1]
      (andIntro hr0 (andIntro hfw hfs)))
    (stepPushOneIntro (ys 4) (mode.relabel j) (gamma.relabel j) (typ.relabel j) (raw.relabel j) (joined.relabel j) ![ys 0,ys 2]
      (andIntro hr0 (andIntro hjw hjs)))

def twoRequest : Program 10 := pairOf (.projection 0) (pairOf (.projection 1) (pairOf (.projection 2) (.projection 3)))
def twoSecond : Program 10 := pairOf (.projection 4) (pairOf (.projection 5) (pairOf (.projection 6) (.projection 7)))
def twoFrontTail : Program 10 := consOf twoSecond (.projection 8)
def twoJoinedTail : Program 10 := consOf twoSecond (.projection 9)
def twoFront : Program 10 := consOf twoRequest twoFrontTail
def twoJoined : Program 10 := consOf twoRequest twoJoinedTail
def twoQueries : Fin 8 → Program 10 := ![twoRequest,twoSecond,twoFrontTail,twoJoinedTail,twoFront,twoJoined,pairOf (InternalLessThan.constantOne 10) twoFront,pairOf (InternalLessThan.constantOne 10) twoJoined]

theorem pushTwoCases (mode₁ gamma₁ typ₁ raw₁ mode₂ gamma₂ typ₂ raw₂ front joined suffix : OTerm alpha) (psi : Formula alpha)
    (ha : Nonempty (Derivation body Delta
      (graph2 InternalApplicationValidityStackAppend.append joined front suffix)))
    (k : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (frontWork joinedWork frontState joinedState : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta
        (graph2 InternalApplicationValidityStackAppend.append joinedWork frontWork (suffix.relabel j))) →
      Nonempty (Derivation body Theta (StepLive frontState frontWork)) →
      Nonempty (Derivation body Theta (StepLive joinedState joinedWork)) →
      Nonempty (Derivation body Theta (StepPushTwo frontState (mode₁.relabel j) (gamma₁.relabel j) (typ₁.relabel j) (raw₁.relabel j) (mode₂.relabel j) (gamma₂.relabel j) (typ₂.relabel j) (raw₂.relabel j) (front.relabel j))) →
      Nonempty (Derivation body Theta (StepPushTwo joinedState (mode₁.relabel j) (gamma₁.relabel j) (typ₁.relabel j) (raw₁.relabel j) (mode₂.relabel j) (gamma₂.relabel j) (typ₂.relabel j) (raw₂.relabel j) (joined.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
  let xs : Fin 10 → OTerm alpha := ![mode₁,gamma₁,typ₁,raw₁,mode₂,gamma₂,typ₂,raw₂,front,joined]
  apply queryCases twoQueries xs psi
  intro beta j ys Theta hj hq
  have ha' := renameInto ha j Theta hj
  rw [graph2Rename] at ha'
  let xx : Fin 10 → OTerm beta := fun i => (xs i).relabel j
  have hr0 := OriginalTypedDecoderInternalRequestProof.requestForward
    (.projection 0) (.projection 1) (.projection 2) (.projection 3)
    (ys 0) (mode₁.relabel j) (gamma₁.relabel j) (typ₁.relabel j) (raw₁.relabel j) xx
    (projectionValue 0 xx) (projectionValue 1 xx)
    (projectionValue 2 xx) (projectionValue 3 xx) (hq 0)
  have hr1 := OriginalTypedDecoderInternalRequestProof.requestForward
    (.projection 4) (.projection 5) (.projection 6) (.projection 7)
    (ys 1) (mode₂.relabel j) (gamma₂.relabel j) (typ₂.relabel j) (raw₂.relabel j) xx
    (projectionValue 4 xx) (projectionValue 5 xx)
    (projectionValue 6 xx) (projectionValue 7 xx) (hq 1)
  have hft := binaryRecover InternalListCodec.consCode twoSecond (.projection 8)
    (ys 2) (ys 1) (front.relabel j) xx (hq 2) (hq 1) (projectionValue 8 xx)
  have hjt := binaryRecover InternalListCodec.consCode twoSecond (.projection 9)
    (ys 3) (ys 1) (joined.relabel j) xx (hq 3) (hq 1) (projectionValue 9 xx)
  have hfw := binaryRecover InternalListCodec.consCode twoRequest twoFrontTail
    (ys 4) (ys 0) (ys 2) xx (hq 4) (hq 0) (hq 2)
  have hjw := binaryRecover InternalListCodec.consCode twoRequest twoJoinedTail
    (ys 5) (ys 0) (ys 3) xx (hq 5) (hq 0) (hq 3)
  have hat := InternalApplicationValidityStackAppendListProof.consBackward
    (ys 2) (ys 1) (front.relabel j) (suffix.relabel j) (joined.relabel j) (ys 3) hft ha' hjt
  have happ := InternalApplicationValidityStackAppendListProof.consBackward
    (ys 4) (ys 0) (ys 2) (suffix.relabel j) (ys 3) (ys 5) hfw hat hjw
  have hfs := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 10) twoFront
    (ys 6) (numeral 1) (ys 4) xx (hq 6) (InternalLessThanSupportProof.oneConstantValue xx) (hq 4)
  have hjs := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 10) twoJoined
    (ys 7) (numeral 1) (ys 5) xx (hq 7) (InternalLessThanSupportProof.oneConstantValue xx) (hq 5)
  exact k beta j Theta (ys 4) (ys 5) (ys 6) (ys 7) hj happ hfs hjs
    (stepPushTwoIntro (ys 6) (mode₁.relabel j) (gamma₁.relabel j) (typ₁.relabel j) (raw₁.relabel j) (mode₂.relabel j) (gamma₂.relabel j) (typ₂.relabel j) (raw₂.relabel j) (front.relabel j) ![ys 0,ys 1,ys 2,ys 4]
      (andIntro hr0 (andIntro hr1 (andIntro hft (andIntro hfw hfs)))))
    (stepPushTwoIntro (ys 7) (mode₁.relabel j) (gamma₁.relabel j) (typ₁.relabel j) (raw₁.relabel j) (mode₂.relabel j) (gamma₂.relabel j) (typ₂.relabel j) (raw₂.relabel j) (joined.relabel j) ![ys 0,ys 1,ys 3,ys 5]
      (andIntro hr0 (andIntro hr1 (andIntro hjt (andIntro hjw hjs)))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingPushProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceCouplingPushProof
