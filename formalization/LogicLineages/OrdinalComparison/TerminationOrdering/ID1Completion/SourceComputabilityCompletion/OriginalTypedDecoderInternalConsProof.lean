module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalConsSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalPushProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalOrdinaryGuardProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalConsProof
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
open OriginalTypedDecoderInternalScalarProof OriginalTypedDecoderInternalBinaryProof
open OriginalTypedDecoderInternalConsSyntaxProof OriginalTypedDecoderInternalPushProof
open OriginalTypedDecoderInternalOrdinaryGuardProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem consForward (state out g t p suffix : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 gamma g state)))
    (ht : Nonempty (Derivation body Delta (graph1 typ t state)))
    (hp : Nonempty (Derivation body Delta (graph1 payload p state)))
    (hr : Nonempty (Derivation body Delta (graph1 rest suffix state)))
    (ho : Nonempty (Derivation body Delta (graph1 consStep out state))) :
    Nonempty (Derivation body Delta (StepArgumentsCons out g t p suffix)) := by
  let qs : Fin 5 → Program 1 := ![domain,firstChild,secondChild,expectedDomain,expectedTail]
  apply queryCases qs (Fin.cons state Fin.elim0) _
  intro beta j ys Theta hj hq
  rw [stepArgumentsConsRename]
  have hg' := renameInto hg j Theta hj
  have ht' := renameInto ht j Theta hj
  have hp' := renameInto hp j Theta hj
  have hr' := renameInto hr j Theta hj
  have ho' := renameInto ho j Theta hj
  simp only [graph1Rename] at hg' ht' hp' hr' ho'
  simp only [consTermRename,emptyRename] at hq
  let xx : Fin 1 → OTerm beta := Fin.cons (state.relabel j) Fin.elim0
  let yes := pushTwo (termRequestOf gamma domain firstChild)
    (argumentsRequestOf gamma expectedTail secondChild)
  let P := programGraph yes (out.relabel j) xx
  let Q := StepPushTwo (out.relabel j) (numeral 0) (g.relabel j) (ys 0) (ys 1)
    (numeral 1) (g.relabel j) (ys 4) (ys 2) (suffix.relabel j)
  have hbinary := binaryFields payload (p.relabel j) (ys 0) (ys 1) (ys 2) xx hp'
    (hq 0) (hq 1) (hq 2)
  have harrow := arrowFields typ (t.relabel j) (ys 3) (ys 4) xx ht' (hq 3) (hq 4)
  have hguard := guardForward typ expectedDomain domain yes
    (out.relabel j) (t.relabel j) (ys 3) (ys 0) xx ht' (hq 3) (hq 0) ho'
  have himp : Nonempty (Derivation body Theta (P.imp Q)) := by
    obtain ⟨d⟩ := pushTwoForward (Delta := P :: Theta) (constant 1 0) gamma domain firstChild
      (constant 1 1) gamma expectedTail secondChild rest
      (out.relabel j) (numeral 0) (g.relabel j) (ys 0) (ys 1)
      (numeral 1) (g.relabel j) (ys 4) (ys 2) (suffix.relabel j) xx
      (constantValue 0 xx) (withHyp hg' _) (withHyp (hq 0) _) (withHyp (hq 1) _)
      (constantValue 1 xx) (withHyp hg' _) (withHyp (hq 4) _) (withHyp (hq 2) _)
      (withHyp hr' _) ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction d⟩
  have hresult := guardSpecMap (out.relabel j) (t.relabel j) (ys 3) (ys 0) P Q himp hguard
  exact stepArgumentsConsIntro _ _ _ _ _ ys (andIntro hbinary (andIntro harrow hresult))

theorem consBackward (state out g t p suffix : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 gamma g state)))
    (ht : Nonempty (Derivation body Delta (graph1 typ t state)))
    (hp : Nonempty (Derivation body Delta (graph1 payload p state)))
    (hr : Nonempty (Derivation body Delta (graph1 rest suffix state)))
    (ho : Nonempty (Derivation body Delta (StepArgumentsCons out g t p suffix))) :
    Nonempty (Derivation body Delta (graph1 consStep out state)) := by
  apply stepArgumentsConsCases out g t p suffix _ ho
  intro beta j Theta ys hj hq
  rw [graph1Rename]
  have hg' := renameInto hg j Theta hj
  have ht' := renameInto ht j Theta hj
  have hp' := renameInto hp j Theta hj
  have hr' := renameInto hr j Theta hj
  simp only [graph1Rename] at hg' ht' hp' hr'
  let xx : Fin 1 → OTerm beta := Fin.cons (state.relabel j) Fin.elim0
  let yes := pushTwo (termRequestOf gamma domain firstChild)
    (argumentsRequestOf gamma expectedTail secondChild)
  let P := programGraph yes (out.relabel j) xx
  let Q := StepPushTwo (out.relabel j) (numeral 0) (g.relabel j) (ys 0) (ys 1)
    (numeral 1) (g.relabel j) (ys 4) (ys 2) (suffix.relabel j)
  have hd := binaryDomainValue payload (p.relabel j) (ys 0) (ys 1) (ys 2) xx hp' (andLeft hq)
  have hf := binaryFirstValue payload (p.relabel j) (ys 0) (ys 1) (ys 2) xx hp' (andLeft hq)
  have hs := binarySecondValue payload (p.relabel j) (ys 0) (ys 1) (ys 2) xx hp' (andLeft hq)
  have he := headValue typ (t.relabel j) (ys 3) (ys 4) xx ht' (andLeft (andRight hq))
  have htail := tailValue typ (t.relabel j) (ys 3) (ys 4) xx ht' (andLeft (andRight hq))
  have himp : Nonempty (Derivation body Theta (Q.imp P)) := by
    obtain ⟨d⟩ := pushTwoBackward (Delta := Q :: Theta) (constant 1 0) gamma domain firstChild
      (constant 1 1) gamma expectedTail secondChild rest
      (out.relabel j) (numeral 0) (g.relabel j) (ys 0) (ys 1)
      (numeral 1) (g.relabel j) (ys 4) (ys 2) (suffix.relabel j) xx
      (constantValue 0 xx) (withHyp hg' _) (withHyp hd _) (withHyp hf _)
      (constantValue 1 xx) (withHyp hg' _) (withHyp htail _) (withHyp hs _)
      (withHyp hr' _) ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction d⟩
  have hguard := guardSpecMap (out.relabel j) (t.relabel j) (ys 3) (ys 0) Q P himp
    (andRight (andRight hq))
  exact guardBackward typ expectedDomain domain yes
    (out.relabel j) (t.relabel j) (ys 3) (ys 0) xx ht' he hd hguard

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalConsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalConsProof
