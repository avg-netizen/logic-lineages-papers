module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceOutputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptancePushProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceLeafSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceUnaryLocalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoder OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalAcceptance
open OriginalTypedDecoderInternalScalarProof OriginalTypedDecoderInternalPushProof
open OriginalTypedDecoderInternalOrdinaryGuardProof
open OriginalTypedDecoderInternalFuelSupportProof (withHyp)
open OriginalTypedDecoderInternalFuelDecreaseLeafProof (choiceCases weakenProof)
open OriginalTypedDecoderInternalAcceptanceLeafSupportProof
open OriginalRawSyntaxTransport (constant)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem acceptedGuard (H : Program 1) (out c x y : OTerm alpha) (P : Formula alpha)
    (hg : Nonempty (Derivation body Gamma (guardSpec out c x y P)))
    (ha : Nonempty (Derivation body Gamma (AcceptedState H out))) :
    Nonempty (Derivation body Gamma ((equal c z).not ⊓ (equal x y ⊓ P))) := by
  apply choiceCases hg
  · intro Delta inc hgood
    exact hgood
  · intro Delta inc hbad
    obtain ⟨hbot⟩ := acceptedRejectImpossible H out (andRight hbad) (weakenProof ha inc)
    exact ⟨Derivation.explosion hbot⟩

theorem lambdaGuardAt (state out g t p d child requestedDomain codomain extended suffix : OTerm alpha)
    (hg : Nonempty (Derivation body Gamma (graph1 gamma g state)))
    (ht : Nonempty (Derivation body Gamma (graph1 typ t state)))
    (hp : Nonempty (Derivation body Gamma (graph1 payload p state)))
    (hr : Nonempty (Derivation body Gamma (graph1 rest suffix state)))
    (hpair : Nonempty (Derivation body Gamma (StepPair p d child)))
    (harrow : Nonempty (Derivation body Gamma (StepArrowFields t requestedDomain codomain)))
    (hext : Nonempty (Derivation body Gamma (StepCons extended d g)))
    (ho : Nonempty (Derivation body Gamma (graph1 lambdaStep out state))) :
    Nonempty (Derivation body Gamma
      (guardSpec out t requestedDomain d (StepPushOne out (numeral 0) extended codomain child suffix))) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  let yes := pushOne (termRequestOf (consOf domain gamma) expectedTail unaryChild)
  have hd := pairLeftValue payload p d child xs hp hpair
  have hb := pairRightValue payload p d child xs hp hpair
  have he := headValue typ t requestedDomain codomain xs ht harrow
  have hf := tailValue typ t requestedDomain codomain xs ht harrow
  have hx := binaryValue InternalListCodec.consCode domain gamma extended d g xs hext hd hg
  have hguard := guardForward typ expectedDomain domain yes out t requestedDomain d xs ht he hd ho
  let P := programGraph yes out xs
  let Q := StepPushOne out (numeral 0) extended codomain child suffix
  have himp : Nonempty (Derivation body Gamma (P.imp Q)) := by
    obtain ⟨h⟩ := pushOneForward (Delta := P :: Gamma) (constant 1 0)
      (consOf domain gamma) expectedTail unaryChild rest out (numeral 0) extended codomain child suffix xs
      (constantValue 0 xs) (withHyp hx P) (withHyp hf P) (withHyp hb P) (withHyp hr P)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction h⟩
  exact guardSpecMap out t requestedDomain d P Q himp hguard

theorem ordinaryGuardAt (H : Program 1)
    (state out g t p head base headData result types suffix : OTerm alpha)
    (hg : Nonempty (Derivation body Gamma (graph1 gamma g state)))
    (ht : Nonempty (Derivation body Gamma (graph1 typ t state)))
    (hp : Nonempty (Derivation body Gamma (graph1 payload p state)))
    (hr : Nonempty (Derivation body Gamma (graph1 rest suffix state)))
    (hpair : Nonempty (Derivation body Gamma (StepPair p head base)))
    (hhead : Nonempty (Derivation body Gamma (programGraph H headData ![head])))
    (hfields : Nonempty (Derivation body Gamma (StepArrowFields headData result types)))
    (ho : Nonempty (Derivation body Gamma (graph1 (ordinaryStep H) out state))) :
    Nonempty (Derivation body Gamma
      (guardSpec out headData result t (StepPushOne out (numeral 1) g types base suffix))) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  let yes := pushOne (argumentsRequestOf gamma (tailOf (ordinarySignature H)) unaryChild)
  have hd := pairLeftValue payload p head base xs hp hpair
  have hb := pairRightValue payload p head base xs hp hpair
  have hsig := unaryValue H domain headData head xs hhead hd
  have he := headValue (ordinarySignature H) headData result types xs hsig hfields
  have hf := tailValue (ordinarySignature H) headData result types xs hsig hfields
  have hguard := guardForward (ordinarySignature H) (headOf (ordinarySignature H)) typ yes
    out headData result t xs hsig he ht ho
  let P := programGraph yes out xs
  let Q := StepPushOne out (numeral 1) g types base suffix
  have himp : Nonempty (Derivation body Gamma (P.imp Q)) := by
    obtain ⟨h⟩ := pushOneForward (Delta := P :: Gamma) (constant 1 1)
      gamma (tailOf (ordinarySignature H)) unaryChild rest out (numeral 1) g types base suffix xs
      (constantValue 1 xs) (withHyp hg P) (withHyp hf P) (withHyp hb P) (withHyp hr P)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction h⟩
  exact guardSpecMap out headData result t P Q himp hguard

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceUnaryLocalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceUnaryLocalProof
