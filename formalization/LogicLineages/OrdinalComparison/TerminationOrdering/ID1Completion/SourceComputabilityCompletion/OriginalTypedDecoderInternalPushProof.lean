module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalPushSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalRequestProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalPushProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof (andIntro andLeft andRight queryCases)
open OriginalTypedDecoder OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderInternalScalarSyntaxProof OriginalTypedDecoderInternalRequestSyntaxProof
open OriginalTypedDecoderInternalPushSyntaxProof OriginalTypedDecoderInternalRequestProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem pushOneForward {n : Nat} (m g t r s : Program n)
    (out mode gamma typ raw rest : OTerm alpha) (xs : Fin n → OTerm alpha)
    (hm : Nonempty (Derivation body Delta (programGraph m mode xs)))
    (hg : Nonempty (Derivation body Delta (programGraph g gamma xs)))
    (ht : Nonempty (Derivation body Delta (programGraph t typ xs)))
    (hr : Nonempty (Derivation body Delta (programGraph r raw xs)))
    (hs : Nonempty (Derivation body Delta (programGraph s rest xs)))
    (ho : Nonempty (Derivation body Delta
      (programGraph (liveOf (consOf (pairOf m (pairOf g (pairOf t r))) s)) out xs))) :
    Nonempty (Derivation body Delta (StepPushOne out mode gamma typ raw rest)) := by
  let request := pairOf m (pairOf g (pairOf t r))
  let work := consOf request s
  apply queryCases (![request,work] : Fin 2 → Program n) xs _
  intro beta j ys Theta hj hq
  rw [stepPushOneRename]
  have hm' := renameInto hm j Theta hj
  have hg' := renameInto hg j Theta hj
  have ht' := renameInto ht j Theta hj
  have hr' := renameInto hr j Theta hj
  have hs' := renameInto hs j Theta hj
  have ho' := renameInto ho j Theta hj
  simp only [programRename] at hm' hg' ht' hr' hs' ho'
  let xx := fun i => (xs i).relabel j
  have hrequest := requestForward m g t r (ys 0) (mode.relabel j) (gamma.relabel j)
    (typ.relabel j) (raw.relabel j) xx hm' hg' ht' hr' (hq 0)
  have hwork := binaryRecover InternalListCodec.consCode request s
    (ys 1) (ys 0) (rest.relabel j) xx (hq 1) (hq 0) hs'
  have hlive := liveForward work (out.relabel j) (ys 1) xx (hq 1) ho'
  exact stepPushOneIntro _ _ _ _ _ _ ys (andIntro hrequest (andIntro hwork hlive))

theorem pushOneBackward {n : Nat} (m g t r s : Program n)
    (out mode gamma typ raw rest : OTerm alpha) (xs : Fin n → OTerm alpha)
    (hm : Nonempty (Derivation body Delta (programGraph m mode xs)))
    (hg : Nonempty (Derivation body Delta (programGraph g gamma xs)))
    (ht : Nonempty (Derivation body Delta (programGraph t typ xs)))
    (hr : Nonempty (Derivation body Delta (programGraph r raw xs)))
    (hs : Nonempty (Derivation body Delta (programGraph s rest xs)))
    (ho : Nonempty (Derivation body Delta (StepPushOne out mode gamma typ raw rest))) :
    Nonempty (Derivation body Delta
      (programGraph (liveOf (consOf (pairOf m (pairOf g (pairOf t r))) s)) out xs)) := by
  apply stepPushOneCases out mode gamma typ raw rest _ ho
  intro beta j Theta ys hj hq
  rw [programRename]
  have hm' := renameInto hm j Theta hj
  have hg' := renameInto hg j Theta hj
  have ht' := renameInto ht j Theta hj
  have hr' := renameInto hr j Theta hj
  have hs' := renameInto hs j Theta hj
  simp only [programRename] at hm' hg' ht' hr' hs'
  let xx := fun i => (xs i).relabel j
  let request := pairOf m (pairOf g (pairOf t r))
  have hrequest := requestBackward m g t r (ys 0) (mode.relabel j) (gamma.relabel j)
    (typ.relabel j) (raw.relabel j) xx hm' hg' ht' hr' (andLeft hq)
  have hwork := binaryValue InternalListCodec.consCode request s
    (ys 1) (ys 0) (rest.relabel j) xx (andLeft (andRight hq)) hrequest hs'
  exact liveBackward (consOf request s) (out.relabel j) (ys 1) xx hwork
    (andRight (andRight hq))

theorem pushTwoForward {n : Nat} (m₁ g₁ t₁ r₁ m₂ g₂ t₂ r₂ s : Program n)
    (out mode₁ gamma₁ typ₁ raw₁ mode₂ gamma₂ typ₂ raw₂ rest : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hm₁ : Nonempty (Derivation body Delta (programGraph m₁ mode₁ xs)))
    (hg₁ : Nonempty (Derivation body Delta (programGraph g₁ gamma₁ xs)))
    (ht₁ : Nonempty (Derivation body Delta (programGraph t₁ typ₁ xs)))
    (hr₁ : Nonempty (Derivation body Delta (programGraph r₁ raw₁ xs)))
    (hm₂ : Nonempty (Derivation body Delta (programGraph m₂ mode₂ xs)))
    (hg₂ : Nonempty (Derivation body Delta (programGraph g₂ gamma₂ xs)))
    (ht₂ : Nonempty (Derivation body Delta (programGraph t₂ typ₂ xs)))
    (hr₂ : Nonempty (Derivation body Delta (programGraph r₂ raw₂ xs)))
    (hs : Nonempty (Derivation body Delta (programGraph s rest xs)))
    (ho : Nonempty (Derivation body Delta
      (programGraph (liveOf (consOf (pairOf m₁ (pairOf g₁ (pairOf t₁ r₁)))
        (consOf (pairOf m₂ (pairOf g₂ (pairOf t₂ r₂))) s))) out xs))) :
    Nonempty (Derivation body Delta
      (StepPushTwo out mode₁ gamma₁ typ₁ raw₁ mode₂ gamma₂ typ₂ raw₂ rest)) := by
  let req₁ := pairOf m₁ (pairOf g₁ (pairOf t₁ r₁))
  let req₂ := pairOf m₂ (pairOf g₂ (pairOf t₂ r₂))
  let suffix := consOf req₂ s
  let work := consOf req₁ suffix
  apply queryCases (![req₁,req₂,suffix,work] : Fin 4 → Program n) xs _
  intro beta j ys Theta hj hq
  rw [stepPushTwoRename]
  have hm₁' := renameInto hm₁ j Theta hj
  have hg₁' := renameInto hg₁ j Theta hj
  have ht₁' := renameInto ht₁ j Theta hj
  have hr₁' := renameInto hr₁ j Theta hj
  have hm₂' := renameInto hm₂ j Theta hj
  have hg₂' := renameInto hg₂ j Theta hj
  have ht₂' := renameInto ht₂ j Theta hj
  have hr₂' := renameInto hr₂ j Theta hj
  have hs' := renameInto hs j Theta hj
  have ho' := renameInto ho j Theta hj
  simp only [programRename] at hm₁' hg₁' ht₁' hr₁' hm₂' hg₂' ht₂' hr₂' hs' ho'
  let xx := fun i => (xs i).relabel j
  have hreq₁ := requestForward m₁ g₁ t₁ r₁ (ys 0) (mode₁.relabel j) (gamma₁.relabel j)
    (typ₁.relabel j) (raw₁.relabel j) xx hm₁' hg₁' ht₁' hr₁' (hq 0)
  have hreq₂ := requestForward m₂ g₂ t₂ r₂ (ys 1) (mode₂.relabel j) (gamma₂.relabel j)
    (typ₂.relabel j) (raw₂.relabel j) xx hm₂' hg₂' ht₂' hr₂' (hq 1)
  have hsuffix := binaryRecover InternalListCodec.consCode req₂ s
    (ys 2) (ys 1) (rest.relabel j) xx (hq 2) (hq 1) hs'
  have hwork := binaryRecover InternalListCodec.consCode req₁ suffix
    (ys 3) (ys 0) (ys 2) xx (hq 3) (hq 0) (hq 2)
  have hlive := liveForward work (out.relabel j) (ys 3) xx (hq 3) ho'
  exact stepPushTwoIntro _ _ _ _ _ _ _ _ _ _ ys
    (andIntro hreq₁ (andIntro hreq₂ (andIntro hsuffix (andIntro hwork hlive))))

theorem pushTwoBackward {n : Nat} (m₁ g₁ t₁ r₁ m₂ g₂ t₂ r₂ s : Program n)
    (out mode₁ gamma₁ typ₁ raw₁ mode₂ gamma₂ typ₂ raw₂ rest : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (hm₁ : Nonempty (Derivation body Delta (programGraph m₁ mode₁ xs)))
    (hg₁ : Nonempty (Derivation body Delta (programGraph g₁ gamma₁ xs)))
    (ht₁ : Nonempty (Derivation body Delta (programGraph t₁ typ₁ xs)))
    (hr₁ : Nonempty (Derivation body Delta (programGraph r₁ raw₁ xs)))
    (hm₂ : Nonempty (Derivation body Delta (programGraph m₂ mode₂ xs)))
    (hg₂ : Nonempty (Derivation body Delta (programGraph g₂ gamma₂ xs)))
    (ht₂ : Nonempty (Derivation body Delta (programGraph t₂ typ₂ xs)))
    (hr₂ : Nonempty (Derivation body Delta (programGraph r₂ raw₂ xs)))
    (hs : Nonempty (Derivation body Delta (programGraph s rest xs)))
    (ho : Nonempty (Derivation body Delta
      (StepPushTwo out mode₁ gamma₁ typ₁ raw₁ mode₂ gamma₂ typ₂ raw₂ rest))) :
    Nonempty (Derivation body Delta
      (programGraph (liveOf (consOf (pairOf m₁ (pairOf g₁ (pairOf t₁ r₁)))
        (consOf (pairOf m₂ (pairOf g₂ (pairOf t₂ r₂))) s))) out xs)) := by
  apply stepPushTwoCases out mode₁ gamma₁ typ₁ raw₁ mode₂ gamma₂ typ₂ raw₂ rest _ ho
  intro beta j Theta ys hj hq
  rw [programRename]
  have hm₁' := renameInto hm₁ j Theta hj
  have hg₁' := renameInto hg₁ j Theta hj
  have ht₁' := renameInto ht₁ j Theta hj
  have hr₁' := renameInto hr₁ j Theta hj
  have hm₂' := renameInto hm₂ j Theta hj
  have hg₂' := renameInto hg₂ j Theta hj
  have ht₂' := renameInto ht₂ j Theta hj
  have hr₂' := renameInto hr₂ j Theta hj
  have hs' := renameInto hs j Theta hj
  simp only [programRename] at hm₁' hg₁' ht₁' hr₁' hm₂' hg₂' ht₂' hr₂' hs'
  let xx := fun i => (xs i).relabel j
  let req₁ := pairOf m₁ (pairOf g₁ (pairOf t₁ r₁))
  let req₂ := pairOf m₂ (pairOf g₂ (pairOf t₂ r₂))
  have hreq₁ := requestBackward m₁ g₁ t₁ r₁ (ys 0) (mode₁.relabel j) (gamma₁.relabel j)
    (typ₁.relabel j) (raw₁.relabel j) xx hm₁' hg₁' ht₁' hr₁' (andLeft hq)
  have hreq₂ := requestBackward m₂ g₂ t₂ r₂ (ys 1) (mode₂.relabel j) (gamma₂.relabel j)
    (typ₂.relabel j) (raw₂.relabel j) xx hm₂' hg₂' ht₂' hr₂' (andLeft (andRight hq))
  have hsuffix := binaryValue InternalListCodec.consCode req₂ s
    (ys 2) (ys 1) (rest.relabel j) xx (andLeft (andRight (andRight hq))) hreq₂ hs'
  have hwork := binaryValue InternalListCodec.consCode req₁ (consOf req₂ s)
    (ys 3) (ys 0) (ys 2) xx (andLeft (andRight (andRight (andRight hq)))) hreq₁ hsuffix
  exact liveBackward (consOf req₁ (consOf req₂ s)) (out.relabel j) (ys 3) xx hwork
    (andRight (andRight (andRight (andRight hq))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalPushProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalPushProof
