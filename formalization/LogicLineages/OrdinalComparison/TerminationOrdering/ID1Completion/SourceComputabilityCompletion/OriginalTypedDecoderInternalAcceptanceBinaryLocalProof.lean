module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceUnaryLocalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptancePushTwoProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceBinaryLocalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoder OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderInternalScalarProof OriginalTypedDecoderInternalBinaryProof
open OriginalTypedDecoderInternalNumberedPayloadProof OriginalTypedDecoderInternalPushProof
open OriginalTypedDecoderInternalOrdinaryGuardProof
open OriginalTypedDecoderInternalAcceptanceBranchProof
open OriginalTypedDecoderInternalTagBranchProof OriginalTypedDecoderInternalModeProof
open OriginalTypedDecoderInternalFuelSupportProof (withHyp)
open OriginalRawSyntaxTransport (constant)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalRawSyntaxTransportInternalConstructorSupportProof (branchNumeralElim)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem argumentsProgramForward (H : Program 1) (i : Fin 8)
    (state workCode request suffix out g t r p : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StepLive state workCode)))
    (hc : Nonempty (Derivation body Gamma (StepCons workCode request suffix)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral 1) g t r)))
    (hp : Nonempty (Derivation body Gamma (StepPair r (numeral i.val) p)))
    (ho : Nonempty (Derivation body Gamma (graph1 (transition H) out state))) :
    Nonempty (Derivation body Gamma (graph1 (argumentsCase i) out state)) := by
  have hv := requestValues state workCode request suffix (numeral 1) g t r (numeral i.val) p hs hc hr hp
  have hm := modeAtForward H state workCode request suffix out hs hc ho
  have h0 := branchNumeralElim 1 0 mode _ (termDispatch H) out (Fin.cons state Fin.elim0) (hv 0) hm
  have hd := branchNumeralElim 1 1 mode _ argumentsDispatch out (Fin.cons state Fin.elim0) (hv 0) h0
  exact argumentsKnownForward state out i (hv 3) hd

theorem applicationPushAt (state out g t p d fn arg arrow suffix : OTerm alpha)
    (hg : Nonempty (Derivation body Gamma (graph1 gamma g state)))
    (ht : Nonempty (Derivation body Gamma (graph1 typ t state)))
    (hp : Nonempty (Derivation body Gamma (graph1 payload p state)))
    (hr : Nonempty (Derivation body Gamma (graph1 rest suffix state)))
    (hpair : Nonempty (Derivation body Gamma (StepBinaryPayload p d fn arg)))
    (harrow : Nonempty (Derivation body Gamma (StepCons arrow d t)))
    (ho : Nonempty (Derivation body Gamma (graph1 applicationStep out state))) :
    Nonempty (Derivation body Gamma
      (StepPushTwo out (numeral 0) g arrow fn (numeral 0) g d arg suffix)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  have hd := binaryDomainValue payload p d fn arg xs hp hpair
  have hf := binaryFirstValue payload p d fn arg xs hp hpair
  have ha := binarySecondValue payload p d fn arg xs hp hpair
  have ht' := binaryValue InternalListCodec.consCode domain typ arrow d t xs harrow hd ht
  exact pushTwoForward (constant 1 0) gamma (consOf domain typ) firstChild
    (constant 1 0) gamma domain secondChild rest out (numeral 0) g arrow fn
    (numeral 0) g d arg suffix xs (constantValue 0 xs) hg ht' hf
    (constantValue 0 xs) hg hd ha hr ho

theorem consGuardAt (state out g t p d head tail requestedDomain tailTypes suffix : OTerm alpha)
    (hg : Nonempty (Derivation body Gamma (graph1 gamma g state)))
    (ht : Nonempty (Derivation body Gamma (graph1 typ t state)))
    (hp : Nonempty (Derivation body Gamma (graph1 payload p state)))
    (hr : Nonempty (Derivation body Gamma (graph1 rest suffix state)))
    (hpair : Nonempty (Derivation body Gamma (StepBinaryPayload p d head tail)))
    (hfields : Nonempty (Derivation body Gamma (StepArrowFields t requestedDomain tailTypes)))
    (ho : Nonempty (Derivation body Gamma (graph1 consStep out state))) :
    Nonempty (Derivation body Gamma
      (guardSpec out t requestedDomain d (StepPushTwo out (numeral 0) g d head (numeral 1) g tailTypes tail suffix))) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  let yes := pushTwo (termRequestOf gamma domain firstChild) (argumentsRequestOf gamma expectedTail secondChild)
  have hd := binaryDomainValue payload p d head tail xs hp hpair
  have hh := binaryFirstValue payload p d head tail xs hp hpair
  have htail := binarySecondValue payload p d head tail xs hp hpair
  have he := headValue typ t requestedDomain tailTypes xs ht hfields
  have hf := tailValue typ t requestedDomain tailTypes xs ht hfields
  have hguard := guardForward typ expectedDomain domain yes out t requestedDomain d xs ht he hd ho
  let P := programGraph yes out xs
  let Q := StepPushTwo out (numeral 0) g d head (numeral 1) g tailTypes tail suffix
  have himp : Nonempty (Derivation body Gamma (P.imp Q)) := by
    obtain ⟨h⟩ := pushTwoForward (Delta := P :: Gamma) (constant 1 0) gamma domain firstChild
      (constant 1 1) gamma expectedTail secondChild rest out (numeral 0) g d head
      (numeral 1) g tailTypes tail suffix xs
      (constantValue 0 xs) (withHyp hg P) (withHyp hd P) (withHyp hh P)
      (constantValue 1 xs) (withHyp hg P) (withHyp hf P) (withHyp htail P) (withHyp hr P)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction h⟩
  exact guardSpecMap out t requestedDomain d P Q himp hguard

theorem numberedGuardAt (H : Program 1)
    (state out g t p label head recorded base extraTypes extras headData headResult baseTypes suffix : OTerm alpha)
    (hg : Nonempty (Derivation body Gamma (graph1 gamma g state)))
    (ht : Nonempty (Derivation body Gamma (graph1 typ t state)))
    (hp : Nonempty (Derivation body Gamma (graph1 payload p state)))
    (hr : Nonempty (Derivation body Gamma (graph1 rest suffix state)))
    (hpair : Nonempty (Derivation body Gamma (StepNumberedPayload p label head recorded base extraTypes extras)))
    (hhead : Nonempty (Derivation body Gamma (programGraph H headData ![head])))
    (hfields : Nonempty (Derivation body Gamma (StepArrowFields headData headResult baseTypes)))
    (ho : Nonempty (Derivation body Gamma (graph1 (numberedStep H) out state))) :
    Nonempty (Derivation body Gamma
      (guardSpec out headData recorded t
        (StepPushTwo out (numeral 1) g baseTypes base (numeral 1) g extraTypes extras suffix))) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons state Fin.elim0
  let yes := pushTwo (argumentsRequestOf gamma (tailOf (numberedSignature H)) numberedBase)
    (argumentsRequestOf gamma numberedTypes numberedExtras)
  have hv := fun i => numberedFieldValue payload i p label head recorded base extraTypes extras xs hp hpair
  have hsig := unaryValue H numberedHead headData head xs hhead (hv 1)
  have hf := tailValue (numberedSignature H) headData headResult baseTypes xs hsig hfields
  have hguard := guardForward (numberedSignature H) numberedType typ yes out headData recorded t xs hsig (hv 2) ht ho
  let P := programGraph yes out xs
  let Q := StepPushTwo out (numeral 1) g baseTypes base (numeral 1) g extraTypes extras suffix
  have himp : Nonempty (Derivation body Gamma (P.imp Q)) := by
    obtain ⟨h⟩ := pushTwoForward (Delta := P :: Gamma) (constant 1 1) gamma (tailOf (numberedSignature H)) numberedBase
      (constant 1 1) gamma numberedTypes numberedExtras rest out (numeral 1) g baseTypes base
      (numeral 1) g extraTypes extras suffix xs
      (constantValue 1 xs) (withHyp hg P) (withHyp hf P) (withHyp (hv 3) P)
      (constantValue 1 xs) (withHyp hg P) (withHyp (hv 4) P) (withHyp (hv 5) P) (withHyp hr P)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction h⟩
  exact guardSpecMap out headData recorded t P Q himp hguard

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceBinaryLocalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceBinaryLocalProof
