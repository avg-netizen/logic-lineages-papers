module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseInductionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseInductionBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalTransparentDecoderValidatorCollapseInduction InternalParameterizedApplicationCertifiedResultFoldClosure OriginalTransparentDecoderValidatorCollapseInductionSyntaxProof
open InternalStrongInduction
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof
open InternalBinderTransportProof InternalDerivationRenamingSyntaxProof
open InternalStrongInductionProof InternalStrongInductionSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem atPayloadIntro (left right : Program 2) (payload : OTerm α)
    (h : Nonempty (Derivation body (Gamma.map (fun p => p.relabel Sum.inl))
      (payloadMatrix left right payload))) :
    Nonempty (Derivation body Gamma (atPayload left right payload)) :=
  InternalClosedProgramsBindingProof.introduction body α 2 Gamma
    (payloadMatrix left right payload) h

theorem atPayloadApply (left right : Program 2) (payload input parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma (atPayload left right payload)))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload input))) :
    Nonempty (Derivation body Gamma (Acceptance left right input parameter)) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body α 2 Gamma
    (payloadMatrix left right payload) (fun i => emb (![input,parameter] i)) h
  rw [payloadMatrixWitness] at h
  obtain ⟨hr⟩ := hr
  exact ⟨Derivation.implicationElimination h hr⟩

theorem belowPayloadAt (left right : Program 2) (payload childPayload : OTerm α)
    (h : Nonempty (Derivation body Gamma (belowPayload left right payload)))
    (hl : Nonempty (Derivation body Gamma (InternalLessThan.strictLess childPayload payload))) :
    Nonempty (Derivation body Gamma (atPayload left right childPayload)) := by
  obtain ⟨h⟩ := h
  obtain ⟨hl⟩ := hl
  have d := Derivation.universalElimination (emb childPayload) h
  change Derivation body Gamma (instantiate
    ((InternalOriginalOrderSyntaxProof.ltF (.var (.inr 0)) (payload.relabel Sum.inl)).imp
      (payloadPredicate left right)) (emb childPayload)) at d
  rw [belowElimSyntax,payloadPredicateInstantiate] at d
  exact ⟨Derivation.implicationElimination d hl⟩

theorem belowPayloadApply (left right : Program 2) (payload childPayload child parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma (belowPayload left right payload)))
    (hl : Nonempty (Derivation body Gamma (InternalLessThan.strictLess childPayload payload)))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right childPayload child))) :
    Nonempty (Derivation body Gamma (Acceptance left right child parameter)) :=
  atPayloadApply left right childPayload child parameter
    (belowPayloadAt left right payload childPayload h hl) hr

/-- The continuation supplies the actual internal induction step at every
context and payload. Strong induction itself is proved in the same calculus. -/
theorem payloadInduction (left right : Program 2) (payload : OTerm α)
    (step : ∀ (β : Type) (Delta : List (Formula β)) (p : OTerm β),
      Nonempty (Derivation body Delta (belowPayload left right p)) →
      Nonempty (Derivation body Delta (atPayload left right p))) :
    Nonempty (Derivation body Gamma (atPayload left right payload)) := by
  let theta : Formula (α ⊕ Fin 1) := payloadPredicate left right
  have hstep : Nonempty (Derivation body
      (InternalStrongInduction.below (lift theta) (.var (.inr 0)) :: Gamma.map weaken) theta) := by
    change Nonempty (Derivation body
      (InternalStrongInduction.below (lift (payloadPredicate left right))
        (.var (.inr 0)) :: Gamma.map weaken)
      (atPayload left right (.var (.inr 0))))
    rw [payloadPredicateLift]
    exact step (α ⊕ Fin 1) _ (.var (.inr 0)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := strongInduction theta hstep
  have e := Derivation.universalElimination (emb payload) d
  change Derivation body Gamma
    (instantiate (payloadPredicate left right) (emb payload)) at e
  rw [payloadPredicateInstantiate] at e
  exact ⟨e⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseInductionBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseInductionBindingProof
