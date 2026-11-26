module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalOrdinarySyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalOrdinaryGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalScalarProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalPushProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalOrdinaryProof
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
open OriginalTypedDecoderInternalOrdinarySyntaxProof OriginalTypedDecoderInternalOrdinaryGuardProof
open OriginalTypedDecoderInternalPushProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

 theorem ordinaryForward (H : Program 1) (state out g t p suffix : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 gamma g state)))
    (ht : Nonempty (Derivation body Delta (graph1 typ t state)))
    (hp : Nonempty (Derivation body Delta (graph1 payload p state)))
    (hr : Nonempty (Derivation body Delta (graph1 rest suffix state)))
    (ho : Nonempty (Derivation body Delta (graph1 (ordinaryStep H) out state))) :
    Nonempty (Derivation body Delta (StepOrdinary H out g t p suffix)) := by
  let qs : Fin 5 → Program 1 :=
    ![domain,unaryChild,ordinarySignature H,headOf (ordinarySignature H),tailOf (ordinarySignature H)]
  apply queryCases qs (Fin.cons state Fin.elim0) _
  intro beta j ys Theta hj hq
  rw [stepOrdinaryRename]
  have hg' := renameInto hg j Theta hj
  have ht' := renameInto ht j Theta hj
  have hp' := renameInto hp j Theta hj
  have hr' := renameInto hr j Theta hj
  have ho' := renameInto ho j Theta hj
  simp only [graph1Rename] at hg' ht' hp' hr' ho'
  simp only [consTermRename,emptyRename] at hq
  let xx : Fin 1 → OTerm beta := Fin.cons (state.relabel j) Fin.elim0
  let good := pushOne (argumentsRequestOf gamma (tailOf (ordinarySignature H)) unaryChild)
  have hpayload := pairFields payload (p.relabel j) (ys 0) (ys 1) xx hp' (hq 0) (hq 1)
  have hsignature := unaryRecover H domain (ys 2) (ys 0) xx (hq 2) (hq 0)
  have hfields := arrowFields (ordinarySignature H) (ys 2) (ys 3) (ys 4) xx (hq 2) (hq 3) (hq 4)
  have hguard := guardForward (ordinarySignature H) (headOf (ordinarySignature H)) typ good
    (out.relabel j) (ys 2) (ys 3) (t.relabel j) xx (hq 2) (hq 3) ht' ho'
  have himp : Nonempty (Derivation body Theta
      ((programGraph good (out.relabel j) xx).imp
        (StepPushOne (out.relabel j) (numeral 1) (g.relabel j) (ys 4) (ys 1) (suffix.relabel j)))) := by
    obtain ⟨hpush⟩ := pushOneForward (Delta := programGraph good (out.relabel j) xx :: Theta) (constant 1 1) gamma (tailOf (ordinarySignature H)) unaryChild rest
      (out.relabel j) (numeral 1) (g.relabel j) (ys 4) (ys 1) (suffix.relabel j) xx
      (constantValue 1 xx) (withHyp hg' _) (withHyp (hq 4) _) (withHyp (hq 1) _) (withHyp hr' _)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction hpush⟩
  have hresult := guardSpecMap (out.relabel j) (ys 2) (ys 3) (t.relabel j) _ _ himp hguard
  exact stepOrdinaryIntro H _ _ _ _ _ ys
    (andIntro hpayload (andIntro hsignature (andIntro hfields hresult)))

 theorem ordinaryBackward (H : Program 1) (state out g t p suffix : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 gamma g state)))
    (ht : Nonempty (Derivation body Delta (graph1 typ t state)))
    (hp : Nonempty (Derivation body Delta (graph1 payload p state)))
    (hr : Nonempty (Derivation body Delta (graph1 rest suffix state)))
    (ho : Nonempty (Derivation body Delta (StepOrdinary H out g t p suffix))) :
    Nonempty (Derivation body Delta (graph1 (ordinaryStep H) out state)) := by
  apply stepOrdinaryCases H out g t p suffix _ ho
  intro beta j Theta ys hj hq
  rw [graph1Rename]
  have hg' := renameInto hg j Theta hj
  have ht' := renameInto ht j Theta hj
  have hp' := renameInto hp j Theta hj
  have hr' := renameInto hr j Theta hj
  simp only [graph1Rename] at hg' ht' hp' hr'
  let xx : Fin 1 → OTerm beta := Fin.cons (state.relabel j) Fin.elim0
  let good := pushOne (argumentsRequestOf gamma (tailOf (ordinarySignature H)) unaryChild)
  have hdomain := pairLeftValue payload (p.relabel j) (ys 0) (ys 1) xx hp' (andLeft hq)
  have hbase := pairRightValue payload (p.relabel j) (ys 0) (ys 1) xx hp' (andLeft hq)
  have hsignature := unaryValue H domain (ys 2) (ys 0) xx (andLeft (andRight hq)) hdomain
  have hhead := headValue (ordinarySignature H) (ys 2) (ys 3) (ys 4) xx hsignature
    (andLeft (andRight (andRight hq)))
  have htail := tailValue (ordinarySignature H) (ys 2) (ys 3) (ys 4) xx hsignature
    (andLeft (andRight (andRight hq)))
  have himp : Nonempty (Derivation body Theta
      ((StepPushOne (out.relabel j) (numeral 1) (g.relabel j) (ys 4) (ys 1) (suffix.relabel j)).imp
        (programGraph good (out.relabel j) xx))) := by
    obtain ⟨hpush⟩ := pushOneBackward (Delta := StepPushOne (out.relabel j) (numeral 1) (g.relabel j) (ys 4) (ys 1) (suffix.relabel j) :: Theta) (constant 1 1) gamma (tailOf (ordinarySignature H)) unaryChild rest
      (out.relabel j) (numeral 1) (g.relabel j) (ys 4) (ys 1) (suffix.relabel j) xx
      (constantValue 1 xx) (withHyp hg' _) (withHyp htail _) (withHyp hbase _) (withHyp hr' _)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction hpush⟩
  have hguard := guardSpecMap (out.relabel j) (ys 2) (ys 3) (t.relabel j) _ _ himp
    (andRight (andRight (andRight hq)))
  exact guardBackward (ordinarySignature H) (headOf (ordinarySignature H)) typ good
    (out.relabel j) (ys 2) (ys 3) (t.relabel j) xx hsignature hhead ht' hguard

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalOrdinaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalOrdinaryProof
