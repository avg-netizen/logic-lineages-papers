module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseInductionBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionTotalityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open OriginalTransparentDecoderValidatorCollapseInduction
open OriginalTransparentDecoderValidatorCollapseInductionSyntaxProof
open OriginalTransparentDecoderValidatorCollapseInductionBindingProof
open InternalGraphCompositionTotalityProof InternalAcceptanceSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- A local payload step is universally closed before strong induction.
All packed inputs and per-frame parameters remain independently quantified. -/
theorem payloadStep (left right : Program 2)
    (step : ∀ (beta : Type) (Delta : List (Formula beta)) (payload raw parameter : OTerm beta),
      Nonempty (Derivation body Delta (belowPayload left right payload)) →
      Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload raw)) →
      Nonempty (Derivation body Delta (Acceptance left right raw parameter)))
    (payload : OTerm alpha)
    (hind : Nonempty (Derivation body Gamma (belowPayload left right payload))) :
    Nonempty (Derivation body Gamma (atPayload left right payload)) := by
  apply atPayloadIntro left right payload
  let raw : OTerm (alpha ⊕ Fin 2) := .var (.inr 0)
  let parameter : OTerm (alpha ⊕ Fin 2) := .var (.inr 1)
  let Delta := graph1 InternalUnpair.right (payload.relabel Sum.inl) raw ::
    Gamma.map (fun q => q.relabel Sum.inl)
  have hind' := renameInto hind (Sum.inl : alpha → alpha ⊕ Fin 2) Delta (by
    intro q hq
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
  rw [belowPayloadRename] at hind'
  obtain ⟨h⟩ := step (alpha ⊕ Fin 2) Delta (payload.relabel Sum.inl) raw parameter hind'
    (show Nonempty (Derivation body Delta
      (graph1 InternalUnpair.right (payload.relabel Sum.inl) raw)) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.implicationIntroduction h⟩

/-- Complete independent strong induction over the actual original payload.
The caller proves only the one-step arithmetic compatibility; no child
acceptance or source/target calibration is hidden in this internal supplier. -/
theorem acceptanceInduction (left right : Program 2)
    (step : ∀ (beta : Type) (Delta : List (Formula beta)) (payload raw parameter : OTerm beta),
      Nonempty (Derivation body Delta (belowPayload left right payload)) →
      Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload raw)) →
      Nonempty (Derivation body Delta (Acceptance left right raw parameter)))
    (raw parameter : OTerm alpha) :
    Nonempty (Derivation body Gamma (Acceptance left right raw parameter)) := by
  apply programCases InternalUnpair.right (Fin.cons raw Fin.elim0) _
  intro beta j Delta payload hj hp
  rw [acceptanceRename]
  simp only [consTermRename,emptyRename] at hp
  have hall := payloadInduction (body := body) (Gamma := Delta) left right payload
    (fun beta Theta p h => payloadStep left right step p h)
  exact atPayloadApply left right payload (raw.relabel j) (parameter.relabel j) hall hp

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseInductionProof
