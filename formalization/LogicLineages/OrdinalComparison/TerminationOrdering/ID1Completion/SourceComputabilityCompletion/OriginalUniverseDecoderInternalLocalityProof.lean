module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalGuardProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalLocalityProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof (andIntro andLeft andRight queryCases)
open InternalOriginalPairingOrderArithmeticProof (withHyp)
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalScalarSyntaxProof
open OriginalTypedDecoderInternalScalarProof OriginalTypedDecoderInternalRequestSyntaxProof
open OriginalUniverseDecoderInternalAcceptanceProof OriginalUniverseDecoderInternalGuardProof
open OriginalUniverseDecoderInternalDecisionProof
open OriginalUniverseDecoderStepSpecification
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The shared raw prefix is opened internally. Both literal requests then
reconstruct exactly the same five inspected fields, regardless of Gamma. -/
theorem localityForward (M W : Program 2)
    (out r₁ r₂ mode gamma₁ gamma₂ typ raw context : OTerm alpha)
    (hr₁ : Nonempty (Derivation body Delta (StepRequest r₁ mode gamma₁ typ raw)))
    (hr₂ : Nonempty (Derivation body Delta (StepRequest r₂ mode gamma₂ typ raw)))
    (ho : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.guard M W) out r₁ context))) :
    Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.guard M W) out r₂ context)) := by
  let p : Program 1 := .projection 0
  let qs : Fin 6 → Program 1 :=
    ![leftOf p,rightOf p,leftOf (rightOf p),rightOf (rightOf p),
      leftOf (rightOf (rightOf p)),rightOf (rightOf (rightOf p))]
  apply queryCases qs (Fin.cons raw Fin.elim0) _
  intro beta j ys Theta hj hq
  rw [graph2Rename]
  have hr₁' := renameInto hr₁ j Theta hj
  have hr₂' := renameInto hr₂ j Theta hj
  have ho' := renameInto ho j Theta hj
  simp only [stepRequestRename] at hr₁' hr₂'
  rw [graph2Rename] at ho'
  simp only [consTermRename,emptyRename] at hq
  let xx : Fin 1 → OTerm beta := Fin.cons (raw.relabel j) Fin.elim0
  have hraw := pairFields p (raw.relabel j) (ys 0) (ys 1) xx (projectionValue 0 xx) (hq 0) (hq 1)
  have hpay := pairFields (rightOf p) (ys 1) (ys 2) (ys 3) xx (hq 1) (hq 2) (hq 3)
  have hrest := pairFields (rightOf (rightOf p)) (ys 3) (ys 4) (ys 5) xx (hq 3) (hq 4) (hq 5)
  have hs₁ := prefixSelectors (r₁.relabel j) (context.relabel j) (mode.relabel j) (gamma₁.relabel j)
    (typ.relabel j) (raw.relabel j) (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) hr₁' hraw hpay hrest
  have hs₂ := prefixSelectors (r₂.relabel j) (context.relabel j) (mode.relabel j) (gamma₂.relabel j)
    (typ.relabel j) (raw.relabel j) (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) hr₂' hraw hpay hrest
  have hi₁ := acceptEquivalence M W (r₁.relabel j) (context.relabel j) (mode.relabel j) (typ.relabel j)
    (ys 0) (ys 2) (ys 4) hs₁.1 hs₁.2.1 hs₁.2.2.1 hs₁.2.2.2.1 hs₁.2.2.2.2
  have hi₂ := acceptEquivalence M W (r₂.relabel j) (context.relabel j) (mode.relabel j) (typ.relabel j)
    (ys 0) (ys 2) (ys 4) hs₂.1 hs₂.2.1 hs₂.2.2.1 hs₂.2.2.2.1 hs₂.2.2.2.2
  let C := guardCondition M W (mode.relabel j) (typ.relabel j) (ys 0) (ys 2) (ys 4) (context.relabel j)
  have hc := decisionForward (guardBoolean M W) (out.relabel j)
    (![r₁.relabel j,context.relabel j] : Fin 2 → OTerm beta) C hi₁ ho'
  exact decisionBackward (guardBoolean M W) (out.relabel j)
    (![r₂.relabel j,context.relabel j] : Fin 2 → OTerm beta) C hi₂ hc

theorem actualOriginalUniverseSymbolicLocality :
    OriginalUniverseDecoderTargets.ActualOriginalUniverseSymbolicLocality := by
  intro M W body alpha out r₁ r₂ mode gamma₁ gamma₂ typ raw context
  let A := StepRequest r₁ mode gamma₁ typ raw ⊓ StepRequest r₂ mode gamma₂ typ raw
  let P := graph2 (OriginalUniverseDecoder.guard M W) out r₁ context
  let Q := graph2 (OriginalUniverseDecoder.guard M W) out r₂ context
  have ha : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hf⟩ := localityForward M W out r₁ r₂ mode gamma₁ gamma₂ typ raw context
    (withHyp (andLeft ha) P) (withHyp (andRight ha) P)
    (show Nonempty (Derivation body [P,A] P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := localityForward M W out r₂ r₁ mode gamma₂ gamma₁ typ raw context
    (withHyp (andRight ha) Q) (withHyp (andLeft ha) Q)
    (show Nonempty (Derivation body [Q,A] Q) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalLocalityProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalLocalityProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalLocalityProof.actualOriginalUniverseSymbolicLocality
