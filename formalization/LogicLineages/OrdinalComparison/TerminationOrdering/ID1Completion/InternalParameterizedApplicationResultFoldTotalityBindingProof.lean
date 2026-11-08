module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalitySyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalityBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalParameterizedApplicationResultFoldTotality InternalParameterizedApplicationCertifiedResultFoldClosure InternalParameterizedApplicationResultFoldTotalitySyntaxProof
open InternalStrongInduction
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof
open InternalBinderTransportProof InternalDerivationRenamingSyntaxProof
open InternalStrongInductionProof InternalStrongInductionSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem hasCertifiedOutputIntro (guard leaf : Program 2) (combine : Program 5) (out input parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (certifiedFoldP guard leaf combine out input parameter))) :
    Nonempty (Derivation body Gamma (hasCertifiedOutputP guard leaf combine input parameter)) := by
  obtain ⟨h⟩ := h
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb out)
  rw [certifiedFoldPInstantiate]
  exact h

/-- Eliminate the original existential; the continuation works in its actual
fresh-variable context and retains every relabeled original hypothesis. -/
theorem hasCertifiedOutputCases (guard leaf : Program 2) (combine : Program 5) (input parameter : OTerm α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (hasCertifiedOutputP guard leaf combine input parameter)))
    (step : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (out : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (certifiedFoldP guard leaf combine out
        (input.relabel j) (parameter.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  obtain ⟨h⟩ := h
  let mat := certifiedFoldP guard leaf combine (.var (.inr (0 : Fin 1)))
    (input.relabel Sum.inl) (parameter.relabel Sum.inl)
  obtain ⟨d⟩ := step (α ⊕ Fin 1) Sum.inl (mat :: Gamma.map weaken) (.var (.inr 0))
    (by intro p hp; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.existentialElimination h d⟩

theorem atPayloadIntro (guard leaf : Program 2) (combine : Program 5) (payload : OTerm α)
    (h : Nonempty (Derivation body (Gamma.map (fun p => p.relabel Sum.inl))
      (payloadMatrixP guard leaf combine payload))) :
    Nonempty (Derivation body Gamma (atPayloadP guard leaf combine payload)) :=
  InternalClosedProgramsBindingProof.introduction body α 2 Gamma
    (payloadMatrixP guard leaf combine payload) h

theorem atPayloadApply (guard leaf : Program 2) (combine : Program 5) (payload input parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma (atPayloadP guard leaf combine payload)))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload input))) :
    Nonempty (Derivation body Gamma (hasCertifiedOutputP guard leaf combine input parameter)) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body α 2 Gamma
    (payloadMatrixP guard leaf combine payload) (fun i => emb (![input,parameter] i)) h
  rw [payloadMatrixWitness] at h
  obtain ⟨hr⟩ := hr
  exact ⟨Derivation.implicationElimination h hr⟩

theorem belowPayloadAt (guard leaf : Program 2) (combine : Program 5) (payload childPayload : OTerm α)
    (h : Nonempty (Derivation body Gamma (belowPayload guard leaf combine payload)))
    (hl : Nonempty (Derivation body Gamma (InternalLessThan.strictLess childPayload payload))) :
    Nonempty (Derivation body Gamma (atPayloadP guard leaf combine childPayload)) := by
  obtain ⟨h⟩ := h
  obtain ⟨hl⟩ := hl
  have d := Derivation.universalElimination (emb childPayload) h
  change Derivation body Gamma (instantiate
    ((InternalOriginalOrderSyntaxProof.ltF (.var (.inr 0)) (payload.relabel Sum.inl)).imp
      (payloadPredicate guard leaf combine)) (emb childPayload)) at d
  rw [belowElimSyntax,payloadPredicateInstantiate] at d
  exact ⟨Derivation.implicationElimination d hl⟩

theorem belowPayloadApply (guard leaf : Program 2) (combine : Program 5) (payload childPayload child parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma (belowPayload guard leaf combine payload)))
    (hl : Nonempty (Derivation body Gamma (InternalLessThan.strictLess childPayload payload)))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right childPayload child))) :
    Nonempty (Derivation body Gamma (hasCertifiedOutputP guard leaf combine child parameter)) :=
  atPayloadApply guard leaf combine childPayload child parameter
    (belowPayloadAt guard leaf combine payload childPayload h hl) hr

/-- The continuation supplies the actual internal induction step at every
context and payload. Strong induction itself is proved in the same calculus. -/
theorem payloadInduction (guard leaf : Program 2) (combine : Program 5) (payload : OTerm α)
    (step : ∀ (β : Type) (Delta : List (Formula β)) (p : OTerm β),
      Nonempty (Derivation body Delta (belowPayload guard leaf combine p)) →
      Nonempty (Derivation body Delta (atPayloadP guard leaf combine p))) :
    Nonempty (Derivation body Gamma (atPayloadP guard leaf combine payload)) := by
  let theta : Formula (α ⊕ Fin 1) := payloadPredicate guard leaf combine
  have hstep : Nonempty (Derivation body
      (InternalStrongInduction.below (lift theta) (.var (.inr 0)) :: Gamma.map weaken) theta) := by
    change Nonempty (Derivation body
      (InternalStrongInduction.below (lift (payloadPredicate guard leaf combine))
        (.var (.inr 0)) :: Gamma.map weaken)
      (atPayloadP guard leaf combine (.var (.inr 0))))
    rw [payloadPredicateLift]
    exact step (α ⊕ Fin 1) _ (.var (.inr 0)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := strongInduction theta hstep
  have e := Derivation.universalElimination (emb payload) d
  change Derivation body Gamma
    (instantiate (payloadPredicate guard leaf combine) (emb payload)) at e
  rw [payloadPredicateInstantiate] at e
  exact ⟨e⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalityBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultFoldTotalityBindingProof
