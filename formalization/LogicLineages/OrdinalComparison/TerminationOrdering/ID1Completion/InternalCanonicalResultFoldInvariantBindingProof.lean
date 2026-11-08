module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariantSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariantBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalCanonicalResultFoldInvariant InternalCanonicalResultFoldInvariantSyntaxProof
open InternalStrongInduction
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof
open InternalBinderTransportProof InternalDerivationRenamingSyntaxProof
open InternalStrongInductionProof InternalStrongInductionSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem hasCertifiedOutputIntro (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (out input typ : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (certifiedOutput old representative member out input typ))) :
    Nonempty (Derivation body Gamma (hasCertifiedOutput old representative member input typ)) := by
  obtain ⟨h⟩ := h
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb out)
  rw [certifiedOutputInstantiate]
  exact h

/-- Eliminate the original existential; the continuation works in its actual
fresh-variable context and retains every relabeled original hypothesis. -/
theorem hasCertifiedOutputCases (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (input typ : OTerm α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (hasCertifiedOutput old representative member input typ)))
    (step : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (out : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (certifiedOutput old representative member out
        (input.relabel j) (typ.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  obtain ⟨h⟩ := h
  let mat := certifiedOutput old representative member (.var (.inr (0 : Fin 1)))
    (input.relabel Sum.inl) (typ.relabel Sum.inl)
  obtain ⟨d⟩ := step (α ⊕ Fin 1) Sum.inl (mat :: Gamma.map weaken) (.var (.inr 0))
    (by intro p hp; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.existentialElimination h d⟩

theorem atPayloadIntro (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (payload : OTerm α)
    (h : Nonempty (Derivation body (Gamma.map (fun p => p.relabel Sum.inl))
      (payloadMatrix old representative member payload))) :
    Nonempty (Derivation body Gamma (atPayload old representative member payload)) :=
  InternalClosedProgramsBindingProof.introduction body α 2 Gamma
    (payloadMatrix old representative member payload) h

theorem atPayloadApply (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (payload input typ : OTerm α)
    (h : Nonempty (Derivation body Gamma (atPayload old representative member payload)))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload input)))
    (hs : Nonempty (Derivation body Gamma (sourcePremises old member input typ))) :
    Nonempty (Derivation body Gamma (hasCertifiedOutput old representative member input typ)) := by
  obtain ⟨h⟩ := InternalClosedProgramsBindingProof.elimination body α 2 Gamma
    (payloadMatrix old representative member payload) (fun i => emb (![input,typ] i)) h
  rw [payloadMatrixWitness] at h
  obtain ⟨hr⟩ := hr
  obtain ⟨hs⟩ := hs
  exact ⟨Derivation.implicationElimination (Derivation.implicationElimination h hr) hs⟩

theorem belowPayloadAt (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (payload childPayload : OTerm α)
    (h : Nonempty (Derivation body Gamma (belowPayload old representative member payload)))
    (hl : Nonempty (Derivation body Gamma (InternalLessThan.strictLess childPayload payload))) :
    Nonempty (Derivation body Gamma (atPayload old representative member childPayload)) := by
  obtain ⟨h⟩ := h
  obtain ⟨hl⟩ := hl
  have d := Derivation.universalElimination (emb childPayload) h
  change Derivation body Gamma (instantiate
    ((InternalOriginalOrderSyntaxProof.ltF (.var (.inr 0)) (payload.relabel Sum.inl)).imp
      (payloadPredicate old representative member)) (emb childPayload)) at d
  rw [belowElimSyntax,payloadPredicateInstantiate] at d
  exact ⟨Derivation.implicationElimination d hl⟩

theorem belowPayloadApply (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (payload childPayload child typ : OTerm α)
    (h : Nonempty (Derivation body Gamma (belowPayload old representative member payload)))
    (hl : Nonempty (Derivation body Gamma (InternalLessThan.strictLess childPayload payload)))
    (hr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right childPayload child)))
    (hs : Nonempty (Derivation body Gamma (sourcePremises old member child typ))) :
    Nonempty (Derivation body Gamma (hasCertifiedOutput old representative member child typ)) :=
  atPayloadApply old representative member childPayload child typ
    (belowPayloadAt old representative member payload childPayload h hl) hr hs

/-- The continuation supplies the actual internal induction step at every
context and payload. Strong induction itself is proved in the same calculus. -/
theorem payloadInduction (old : InternalOriginalStepGuard.Data)
    (representative member : Program 1) (payload : OTerm α)
    (step : ∀ (β : Type) (Delta : List (Formula β)) (p : OTerm β),
      Nonempty (Derivation body Delta (belowPayload old representative member p)) →
      Nonempty (Derivation body Delta (atPayload old representative member p))) :
    Nonempty (Derivation body Gamma (atPayload old representative member payload)) := by
  let theta : Formula (α ⊕ Fin 1) := payloadPredicate old representative member
  have hstep : Nonempty (Derivation body
      (InternalStrongInduction.below (lift theta) (.var (.inr 0)) :: Gamma.map weaken) theta) := by
    change Nonempty (Derivation body
      (InternalStrongInduction.below (lift (payloadPredicate old representative member))
        (.var (.inr 0)) :: Gamma.map weaken)
      (atPayload old representative member (.var (.inr 0))))
    rw [payloadPredicateLift]
    exact step (α ⊕ Fin 1) _ (.var (.inr 0)) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := strongInduction theta hstep
  have e := Derivation.universalElimination (emb payload) d
  change Derivation body Gamma
    (instantiate (payloadPredicate old representative member) (emb payload)) at e
  rw [payloadPredicateInstantiate] at e
  exact ⟨e⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariantBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldInvariantBindingProof
