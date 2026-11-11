module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalVariableSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalRequestProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalVariableProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalAcceptanceSupportProof
open OriginalLambdaConstructorGraphSyntaxProof (andIntro andLeft andRight)
open InternalQuotientComparisonProof (orLeft orRight)
open InternalOriginalPairingOrderArithmeticProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport (constant)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalTypedDecoder OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderInternalVariableSyntaxProof
open OriginalTypedDecoderInternalBranchProof OriginalTypedDecoderInternalRequestProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem variableCallForward (state value g t p : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 gamma g state)))
    (ht : Nonempty (Derivation body Delta (graph1 typ t state)))
    (hp : Nonempty (Derivation body Delta (graph1 payload p state)))
    (hv : Nonempty (Derivation body Delta (graph1 variableCheck value state))) :
    Nonempty (Derivation body Delta (OriginalVariableDecoder.graph value t p g)) := by
  apply compositionRecover OriginalVariableDecoder.check ![typ,payload,gamma] value
    (Fin.cons state Fin.elim0) (Fin.cons t (Fin.cons p (Fin.cons g Fin.elim0))) hv
  intro i
  exact Fin.cases ht (Fin.cases hp (Fin.cases hg (fun k => Fin.elim0 k))) i

theorem variableCallBackward (state value g t p : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 gamma g state)))
    (ht : Nonempty (Derivation body Delta (graph1 typ t state)))
    (hp : Nonempty (Derivation body Delta (graph1 payload p state)))
    (hv : Nonempty (Derivation body Delta (OriginalVariableDecoder.graph value t p g))) :
    Nonempty (Derivation body Delta (graph1 variableCheck value state)) := by
  apply compositionValue OriginalVariableDecoder.check ![typ,payload,gamma] value
    (Fin.cons state Fin.elim0) (Fin.cons t (Fin.cons p (Fin.cons g Fin.elim0))) hv
  intro i
  exact Fin.cases ht (Fin.cases hp (Fin.cases hg (fun k => Fin.elim0 k))) i

theorem variableForward (state out g t p suffix : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 gamma g state)))
    (ht : Nonempty (Derivation body Delta (graph1 typ t state)))
    (hp : Nonempty (Derivation body Delta (graph1 payload p state)))
    (hr : Nonempty (Derivation body Delta (graph1 rest suffix state)))
    (ho : Nonempty (Derivation body Delta (graph1 variableStep out state))) :
    Nonempty (Derivation body Delta (StepVariable out g t p suffix)) := by
  apply programCases variableCheck (Fin.cons state Fin.elim0) _
  intro beta j Theta value hj hv
  rw [stepVariableRename]
  have hg' := renameInto hg j Theta hj
  have ht' := renameInto ht j Theta hj
  have hp' := renameInto hp j Theta hj
  have hr' := renameInto hr j Theta hj
  have ho' := renameInto ho j Theta hj
  simp only [graph1Rename] at hg' ht' hp' hr' ho'
  simp only [consTermRename,emptyRename] at hv
  let xx : Fin 1 → OTerm beta := Fin.cons (state.relabel j) Fin.elim0
  have hcall := variableCallForward (state.relabel j) value (g.relabel j) (t.relabel j)
    (p.relabel j) hg' ht' hp' hv
  have hc := sameForward variableCheck (constant 1 1) pop (constant 1 0)
    (out.relabel j) value (numeral 1) xx hv (constantValue 1 xx) ho'
  apply stepVariableIntro _ _ _ _ _ value
  apply andIntro hcall
  apply orCases hc
  · have hh : Nonempty (Derivation body
        ((equal value (numeral 1) ⊓ programGraph pop (out.relabel j) xx) :: Theta)
        (equal value (numeral 1) ⊓ programGraph pop (out.relabel j) xx)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨he⟩ := andLeft hh
    obtain ⟨hl⟩ := liveForward rest (out.relabel j) (suffix.relabel j) xx
      (withHyp hr' _) (andRight hh)
    exact ⟨orLeft (Derivation.conjunctionIntroduction he hl)⟩
  · have hh : Nonempty (Derivation body
        (((equal value (numeral 1)).not ⊓ programGraph (constant 1 0) (out.relabel j) xx) :: Theta)
        ((equal value (numeral 1)).not ⊓ programGraph (constant 1 0) (out.relabel j) xx)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨he⟩ := andLeft hh
    obtain ⟨hz⟩ := constantForward 0 (out.relabel j) xx (andRight hh)
    exact ⟨orRight (Derivation.conjunctionIntroduction he hz)⟩

theorem variableBackward (state out g t p suffix : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 gamma g state)))
    (ht : Nonempty (Derivation body Delta (graph1 typ t state)))
    (hp : Nonempty (Derivation body Delta (graph1 payload p state)))
    (hr : Nonempty (Derivation body Delta (graph1 rest suffix state)))
    (ho : Nonempty (Derivation body Delta (StepVariable out g t p suffix))) :
    Nonempty (Derivation body Delta (graph1 variableStep out state)) := by
  apply stepVariableCases out g t p suffix _ ho
  intro beta j Theta value hj hv
  rw [graph1Rename]
  have hg' := renameInto hg j Theta hj
  have ht' := renameInto ht j Theta hj
  have hp' := renameInto hp j Theta hj
  have hr' := renameInto hr j Theta hj
  simp only [graph1Rename] at hg' ht' hp' hr'
  let xx : Fin 1 → OTerm beta := Fin.cons (state.relabel j) Fin.elim0
  have hcall := variableCallBackward (state.relabel j) value (g.relabel j) (t.relabel j)
    (p.relabel j) hg' ht' hp' (andLeft hv)
  apply orCases (andRight hv)
  · have hh : Nonempty (Derivation body
        ((equal value (numeral 1) ⊓ StepLive (out.relabel j) (suffix.relabel j)) :: Theta)
        (equal value (numeral 1) ⊓ StepLive (out.relabel j) (suffix.relabel j))) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact sameYesIntro variableCheck (constant 1 1) pop (constant 1 0)
      (out.relabel j) value (numeral 1) xx (withHyp hcall _) (constantValue 1 xx) (andLeft hh)
      (liveBackward rest (out.relabel j) (suffix.relabel j) xx (withHyp hr' _) (andRight hh))
  · have hh : Nonempty (Derivation body
        (((equal value (numeral 1)).not ⊓ equal (out.relabel j) (numeral 0)) :: Theta)
        ((equal value (numeral 1)).not ⊓ equal (out.relabel j) (numeral 0))) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact sameNoIntro variableCheck (constant 1 1) pop (constant 1 0)
      (out.relabel j) value (numeral 1) xx (withHyp hcall _) (constantValue 1 xx) (andLeft hh)
      (constantBackward 0 (out.relabel j) xx (andRight hh))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalVariableProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalVariableProof
