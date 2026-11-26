module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalNumberedSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalNumberedPayloadProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalOrdinaryGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalPushProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalNumberedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof (andIntro andLeft andRight queryCases)
open InternalOriginalPairingOrderArithmeticProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport (constant)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalTypedDecoder OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderInternalScalarSyntaxProof OriginalTypedDecoderInternalScalarProof
open OriginalTypedDecoderInternalNumberedSyntaxProof OriginalTypedDecoderInternalNumberedPayloadProof
open OriginalTypedDecoderInternalOrdinaryGuardProof OriginalTypedDecoderInternalPushProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

 theorem numberedForward (H : Program 1) (state out g t p suffix : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 gamma g state)))
    (ht : Nonempty (Derivation body Delta (graph1 typ t state)))
    (hp : Nonempty (Derivation body Delta (graph1 payload p state)))
    (hr : Nonempty (Derivation body Delta (graph1 rest suffix state)))
    (ho : Nonempty (Derivation body Delta (graph1 (numberedStep H) out state))) :
    Nonempty (Derivation body Delta (StepNumbered H out g t p suffix)) := by
  let qs : Fin 9 → Program 1 :=
    ![leftOf payload,numberedHead,numberedType,numberedBase,numberedTypes,numberedExtras,
      numberedSignature H,headOf (numberedSignature H),tailOf (numberedSignature H)]
  apply queryCases qs (Fin.cons state Fin.elim0) _
  intro beta j ys Theta hj hq
  rw [stepNumberedRename]
  have hg' := renameInto hg j Theta hj
  have ht' := renameInto ht j Theta hj
  have hp' := renameInto hp j Theta hj
  have hr' := renameInto hr j Theta hj
  have ho' := renameInto ho j Theta hj
  simp only [graph1Rename] at hg' ht' hp' hr' ho'
  simp only [consTermRename,emptyRename] at hq
  let xx : Fin 1 → OTerm beta := Fin.cons (state.relabel j) Fin.elim0
  let good := pushTwo (argumentsRequestOf gamma (tailOf (numberedSignature H)) numberedBase)
    (argumentsRequestOf gamma numberedTypes numberedExtras)
  have hpayload := numberedFields payload (p.relabel j) (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5)
    xx hp' (by
      intro i
      refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => ?_))))) i
      · exact hq 0
      · exact hq 1
      · exact hq 2
      · exact hq 3
      · exact hq 4
      · obtain rfl : k = 0 := Fin.eq_zero k
        exact hq 5)
  have hsignature := unaryRecover H numberedHead (ys 6) (ys 1) xx (hq 6) (hq 1)
  have hfields := arrowFields (numberedSignature H) (ys 6) (ys 7) (ys 8) xx (hq 6) (hq 7) (hq 8)
  have hguard := guardForward (numberedSignature H) numberedType typ good
    (out.relabel j) (ys 6) (ys 2) (t.relabel j) xx (hq 6) (hq 2) ht' ho'
  have himp : Nonempty (Derivation body Theta
      ((programGraph good (out.relabel j) xx).imp
        (StepPushTwo (out.relabel j) (numeral 1) (g.relabel j) (ys 8) (ys 3)
          (numeral 1) (g.relabel j) (ys 4) (ys 5) (suffix.relabel j)))) := by
    obtain ⟨hpush⟩ := pushTwoForward (Delta := programGraph good (out.relabel j) xx :: Theta) (constant 1 1) gamma (tailOf (numberedSignature H)) numberedBase
      (constant 1 1) gamma numberedTypes numberedExtras rest
      (out.relabel j) (numeral 1) (g.relabel j) (ys 8) (ys 3)
      (numeral 1) (g.relabel j) (ys 4) (ys 5) (suffix.relabel j) xx
      (constantValue 1 xx) (withHyp hg' _) (withHyp (hq 8) _) (withHyp (hq 3) _)
      (constantValue 1 xx) (withHyp hg' _) (withHyp (hq 4) _) (withHyp (hq 5) _) (withHyp hr' _)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction hpush⟩
  have hresult := guardSpecMap (out.relabel j) (ys 6) (ys 2) (t.relabel j) _ _ himp hguard
  exact stepNumberedIntro H _ _ _ _ _ ys
    (andIntro hpayload (andIntro hsignature (andIntro hfields hresult)))

 theorem numberedBackward (H : Program 1) (state out g t p suffix : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 gamma g state)))
    (ht : Nonempty (Derivation body Delta (graph1 typ t state)))
    (hp : Nonempty (Derivation body Delta (graph1 payload p state)))
    (hr : Nonempty (Derivation body Delta (graph1 rest suffix state)))
    (ho : Nonempty (Derivation body Delta (StepNumbered H out g t p suffix))) :
    Nonempty (Derivation body Delta (graph1 (numberedStep H) out state)) := by
  apply stepNumberedCases H out g t p suffix _ ho
  intro beta j Theta ys hj hq
  rw [graph1Rename]
  have hg' := renameInto hg j Theta hj
  have ht' := renameInto ht j Theta hj
  have hp' := renameInto hp j Theta hj
  have hr' := renameInto hr j Theta hj
  simp only [graph1Rename] at hg' ht' hp' hr'
  let xx : Fin 1 → OTerm beta := Fin.cons (state.relabel j) Fin.elim0
  let good := pushTwo (argumentsRequestOf gamma (tailOf (numberedSignature H)) numberedBase)
    (argumentsRequestOf gamma numberedTypes numberedExtras)
  have hv := fun i => numberedFieldValue payload i (p.relabel j)
    (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) xx hp' (andLeft hq)
  have hsignature := unaryValue H numberedHead (ys 6) (ys 1) xx (andLeft (andRight hq)) (hv 1)
  have htail := tailValue (numberedSignature H) (ys 6) (ys 7) (ys 8) xx hsignature
    (andLeft (andRight (andRight hq)))
  have himp : Nonempty (Derivation body Theta
      ((StepPushTwo (out.relabel j) (numeral 1) (g.relabel j) (ys 8) (ys 3)
          (numeral 1) (g.relabel j) (ys 4) (ys 5) (suffix.relabel j)).imp
        (programGraph good (out.relabel j) xx))) := by
    obtain ⟨hpush⟩ := pushTwoBackward (Delta := StepPushTwo (out.relabel j) (numeral 1) (g.relabel j) (ys 8) (ys 3) (numeral 1) (g.relabel j) (ys 4) (ys 5) (suffix.relabel j) :: Theta) (constant 1 1) gamma (tailOf (numberedSignature H)) numberedBase
      (constant 1 1) gamma numberedTypes numberedExtras rest
      (out.relabel j) (numeral 1) (g.relabel j) (ys 8) (ys 3)
      (numeral 1) (g.relabel j) (ys 4) (ys 5) (suffix.relabel j) xx
      (constantValue 1 xx) (withHyp hg' _) (withHyp htail _) (withHyp (hv 3) _)
      (constantValue 1 xx) (withHyp hg' _) (withHyp (hv 4) _) (withHyp (hv 5) _) (withHyp hr' _)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction hpush⟩
  have hguard := guardSpecMap (out.relabel j) (ys 6) (ys 2) (t.relabel j) _ _ himp
    (andRight (andRight (andRight hq)))
  exact guardBackward (numberedSignature H) numberedType typ good
    (out.relabel j) (ys 6) (ys 2) (t.relabel j) xx hsignature (hv 2) ht' hguard

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalNumberedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalNumberedProof
