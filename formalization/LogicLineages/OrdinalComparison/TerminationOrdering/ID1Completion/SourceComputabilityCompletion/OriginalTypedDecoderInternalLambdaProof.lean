module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLambdaSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalScalarProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalPushProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalOrdinaryGuardProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLambdaProof
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
open OriginalTypedDecoderInternalScalarProof OriginalTypedDecoderInternalLambdaSyntaxProof
open OriginalTypedDecoderInternalPushProof OriginalTypedDecoderInternalOrdinaryGuardProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem lambdaForward (state out g t p suffix : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 gamma g state)))
    (ht : Nonempty (Derivation body Delta (graph1 typ t state)))
    (hp : Nonempty (Derivation body Delta (graph1 payload p state)))
    (hr : Nonempty (Derivation body Delta (graph1 rest suffix state)))
    (ho : Nonempty (Derivation body Delta (graph1 lambdaStep out state))) :
    Nonempty (Derivation body Delta (StepLambda out g t p suffix)) := by
  let qs : Fin 5 → Program 1 := ![domain,unaryChild,expectedDomain,expectedTail,consOf domain gamma]
  apply queryCases qs (Fin.cons state Fin.elim0) _
  intro beta j ys Theta hj hq
  rw [stepLambdaRename]
  have hg' := renameInto hg j Theta hj
  have ht' := renameInto ht j Theta hj
  have hp' := renameInto hp j Theta hj
  have hr' := renameInto hr j Theta hj
  have ho' := renameInto ho j Theta hj
  simp only [graph1Rename] at hg' ht' hp' hr' ho'
  simp only [consTermRename,emptyRename] at hq
  let xx : Fin 1 → OTerm beta := Fin.cons (state.relabel j) Fin.elim0
  let yes := pushOne (termRequestOf (consOf domain gamma) expectedTail unaryChild)
  let P := programGraph yes (out.relabel j) xx
  let Q := StepPushOne (out.relabel j) (numeral 0) (ys 4) (ys 3) (ys 1) (suffix.relabel j)
  have hpair := pairFields payload (p.relabel j) (ys 0) (ys 1) xx hp' (hq 0) (hq 1)
  have harrow := arrowFields typ (t.relabel j) (ys 2) (ys 3) xx ht' (hq 2) (hq 3)
  have hext := binaryRecover InternalListCodec.consCode domain gamma
    (ys 4) (ys 0) (g.relabel j) xx (hq 4) (hq 0) hg'
  have hguard := guardForward typ expectedDomain domain yes
    (out.relabel j) (t.relabel j) (ys 2) (ys 0) xx ht' (hq 2) (hq 0) ho'
  have himp : Nonempty (Derivation body Theta (P.imp Q)) := by
    obtain ⟨d⟩ := pushOneForward (Delta := P :: Theta) (constant 1 0)
      (consOf domain gamma) expectedTail unaryChild rest
      (out.relabel j) (numeral 0) (ys 4) (ys 3) (ys 1) (suffix.relabel j) xx
      (constantValue 0 xx) (withHyp (hq 4) _) (withHyp (hq 3) _)
      (withHyp (hq 1) _) (withHyp hr' _) ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction d⟩
  have hresult := guardSpecMap (out.relabel j) (t.relabel j) (ys 2) (ys 0) P Q himp hguard
  exact stepLambdaIntro _ _ _ _ _ ys (andIntro hpair (andIntro harrow (andIntro hext hresult)))

theorem lambdaBackward (state out g t p suffix : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 gamma g state)))
    (ht : Nonempty (Derivation body Delta (graph1 typ t state)))
    (hp : Nonempty (Derivation body Delta (graph1 payload p state)))
    (hr : Nonempty (Derivation body Delta (graph1 rest suffix state)))
    (ho : Nonempty (Derivation body Delta (StepLambda out g t p suffix))) :
    Nonempty (Derivation body Delta (graph1 lambdaStep out state)) := by
  apply stepLambdaCases out g t p suffix _ ho
  intro beta j Theta ys hj hq
  rw [graph1Rename]
  have hg' := renameInto hg j Theta hj
  have ht' := renameInto ht j Theta hj
  have hp' := renameInto hp j Theta hj
  have hr' := renameInto hr j Theta hj
  simp only [graph1Rename] at hg' ht' hp' hr'
  let xx : Fin 1 → OTerm beta := Fin.cons (state.relabel j) Fin.elim0
  let yes := pushOne (termRequestOf (consOf domain gamma) expectedTail unaryChild)
  let P := programGraph yes (out.relabel j) xx
  let Q := StepPushOne (out.relabel j) (numeral 0) (ys 4) (ys 3) (ys 1) (suffix.relabel j)
  have hd := pairLeftValue payload (p.relabel j) (ys 0) (ys 1) xx hp' (andLeft hq)
  have hb := pairRightValue payload (p.relabel j) (ys 0) (ys 1) xx hp' (andLeft hq)
  have he := headValue typ (t.relabel j) (ys 2) (ys 3) xx ht' (andLeft (andRight hq))
  have hf := tailValue typ (t.relabel j) (ys 2) (ys 3) xx ht' (andLeft (andRight hq))
  have hext := binaryValue InternalListCodec.consCode domain gamma
    (ys 4) (ys 0) (g.relabel j) xx (andLeft (andRight (andRight hq))) hd hg'
  have himp : Nonempty (Derivation body Theta (Q.imp P)) := by
    obtain ⟨d⟩ := pushOneBackward (Delta := Q :: Theta) (constant 1 0)
      (consOf domain gamma) expectedTail unaryChild rest
      (out.relabel j) (numeral 0) (ys 4) (ys 3) (ys 1) (suffix.relabel j) xx
      (constantValue 0 xx) (withHyp hext _) (withHyp hf _)
      (withHyp hb _) (withHyp hr' _) ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction d⟩
  have hguard := guardSpecMap (out.relabel j) (t.relabel j) (ys 2) (ys 0) Q P himp
    (andRight (andRight (andRight hq)))
  exact guardBackward typ expectedDomain domain yes
    (out.relabel j) (t.relabel j) (ys 2) (ys 0) xx ht' he hd hguard

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLambdaProof
