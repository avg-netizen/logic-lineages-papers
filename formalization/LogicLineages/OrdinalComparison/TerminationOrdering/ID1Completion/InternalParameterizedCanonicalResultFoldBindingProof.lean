module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalParameterizedCanonicalResultFold InternalParameterizedCanonicalResultFoldSyntaxProof
open InternalStrongInduction InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof
open InternalBinderTransportProof InternalDerivationRenamingSyntaxProof
open InternalStrongInductionProof InternalStrongInductionSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem hasCertifiedOutputIntro (data : Data) (out input typ parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma (certifiedOutput data out input typ parameter))) :
    Nonempty (Derivation body Gamma (hasCertifiedOutput data input typ parameter)) := by
  obtain ⟨h⟩ := h
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb out)
  rw [certifiedOutputInstantiate]
  exact h

theorem hasCertifiedOutputCases (data : Data)
    (input typ parameter : OTerm α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (hasCertifiedOutput data input typ parameter)))
    (step : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (out : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (certifiedOutput data out
        (input.relabel j) (typ.relabel j) (parameter.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  obtain ⟨h⟩ := h
  let mat := certifiedOutput data (.var (.inr (0 : Fin 1)))
    (input.relabel Sum.inl) (typ.relabel Sum.inl) (parameter.relabel Sum.inl)
  obtain ⟨d⟩ := step (α ⊕ Fin 1) Sum.inl (mat :: Gamma.map weaken) (.var (.inr 0))
    (by intro p hp; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.existentialElimination h d⟩

theorem atPayloadIntro (data : Data) (payload : OTerm α)
    (h : Nonempty (Derivation body (Gamma.map (fun p => p.relabel Sum.inl))
      (payloadMatrix data payload))) :
    Nonempty (Derivation body Gamma (atPayload data payload)) :=
  InternalClosedProgramsBindingProof.introduction body α 3 Gamma (payloadMatrix data payload) h

theorem atPayloadApply (data : Data) (payload input typ parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma (atPayload data payload)))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload input)))
    (hs : Nonempty (Derivation body Gamma (sourcePremises data input typ parameter))) :
    Nonempty (Derivation body Gamma (hasCertifiedOutput data input typ parameter)) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body α 3 Gamma
    (payloadMatrix data payload) (fun i => emb (![input,typ,parameter] i)) h
  rw [payloadMatrixWitness] at h
  obtain ⟨hr⟩ := hr
  obtain ⟨hs⟩ := hs
  exact ⟨Derivation.implicationElimination (Derivation.implicationElimination h hr) hs⟩

theorem belowPayloadAt (data : Data) (payload childPayload : OTerm α)
    (h : Nonempty (Derivation body Gamma (belowPayload data payload)))
    (hl : Nonempty (Derivation body Gamma (InternalLessThan.strictLess childPayload payload))) :
    Nonempty (Derivation body Gamma (atPayload data childPayload)) := by
  obtain ⟨h⟩ := h
  obtain ⟨hl⟩ := hl
  have d := Derivation.universalElimination (emb childPayload) h
  change Derivation body Gamma (instantiate
    ((InternalOriginalOrderSyntaxProof.ltF (.var (.inr 0)) (payload.relabel Sum.inl)).imp
      (payloadPredicate data)) (emb childPayload)) at d
  rw [belowElimSyntax,payloadPredicateInstantiate] at d
  exact ⟨Derivation.implicationElimination d hl⟩

theorem belowPayloadApply (data : Data) (payload childPayload child typ parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma (belowPayload data payload)))
    (hl : Nonempty (Derivation body Gamma (InternalLessThan.strictLess childPayload payload)))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right childPayload child)))
    (hs : Nonempty (Derivation body Gamma (sourcePremises data child typ parameter))) :
    Nonempty (Derivation body Gamma (hasCertifiedOutput data child typ parameter)) :=
  atPayloadApply data childPayload child typ parameter (belowPayloadAt data payload childPayload h hl) hr hs

/-- The sole induction bound is the original payload. All three packed-input,
type and parameter coordinates stay universally bound inside the predicate. -/
theorem payloadInduction (data : Data) (payload : OTerm α)
    (step : ∀ (β : Type) (Delta : List (Formula β)) (p : OTerm β),
      Nonempty (Derivation body Delta (belowPayload data p)) →
      Nonempty (Derivation body Delta (atPayload data p))) :
    Nonempty (Derivation body Gamma (atPayload data payload)) := by
  let theta : Formula (α ⊕ Fin 1) := payloadPredicate data
  have hstep : Nonempty (Derivation body
      (InternalStrongInduction.below (lift theta) (.var (.inr 0)) :: Gamma.map weaken) theta) := by
    change Nonempty (Derivation body
      (InternalStrongInduction.below (lift (payloadPredicate data))
        (.var (.inr 0)) :: Gamma.map weaken) (atPayload data (.var (.inr 0))))
    rw [payloadPredicateLift]
    exact step (α ⊕ Fin 1) _ (.var (.inr 0)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := strongInduction theta hstep
  have e := Derivation.universalElimination (emb payload) d
  change Derivation body Gamma (instantiate (payloadPredicate data) (emb payload)) at e
  rw [payloadPredicateInstantiate] at e
  exact ⟨e⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldBindingProof
