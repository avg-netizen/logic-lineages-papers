module
public import LogicLineages.OrdinalComparison.SourceExistentialPlanCompilationProof
public import LogicLineages.OrdinalComparison.SourceAggregateCompletionProof
public import LogicLineages.OrdinalComparison.SourceGroundEquivalenceProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ExistentialPlan.Proof
open OriginalDomain GroundEquivalence SourceCollisionCompletion

theorem holds_raw {Γ} (r : Result Γ) (ρ : Variable r.context .ground → Nat) :
    r.Holds ρ ↔ SourceAggregateCompletion.AllEqual (valuation (UnitObservation.substitution ρ))
      (ScopedDAG.equations r.forest) := by
  constructor
  · intro h e he
    obtain ⟨e',he',heq⟩ := List.mem_map.mp he
    subst e
    exact (equation_raw ρ e'.1.term e'.2.term).mp (h e' he')
  · intro h e he
    apply (equation_raw ρ e.1.term e.2.term).mpr
    exact h (e.1.term,e.2.term) (List.mem_map.mpr ⟨e,he,rfl⟩)

theorem strict_at {Γ} (q : Plan Γ) (ρ : Variable (compile q).context .ground → Nat) :
    rawScalar (valuation (UnitObservation.substitution ρ)) (strictPair q).1.term <
      rawScalar (valuation (UnitObservation.substitution ρ)) (strictPair q).2.term ↔
      ¬ (compile q).Holds ρ := by
  have ht := (ScopedDAG.Proof.aggregate (compile q).context (compile q).forest).1
  have hl := congrArg Prod.fst ht
  have hr := congrArg Prod.snd ht
  dsimp only at hl hr
  change rawScalar _ (ScopedDAG.aggregate (compile q).forest).2.term <
    rawScalar _ (ScopedDAG.aggregate (compile q).forest).1.term ↔ _
  rw [hl,hr]
  have ha := SourceAggregateCompletion.Proof.admissible_aggregate (compile q).context
    (ScopedDAG.equations (compile q).forest) (UnitObservation.substitution ρ)
  constructor
  · intro hs hh
    have he := ha.2.1.mpr ((holds_raw (compile q) ρ).mp hh)
    omega
  · intro hn
    have he : rawScalar (valuation (UnitObservation.substitution ρ))
        (SourceAggregateCompletion.aggregate (ScopedDAG.equations (compile q).forest)).1 ≠
      rawScalar (valuation (UnitObservation.substitution ρ))
        (SourceAggregateCompletion.aggregate (ScopedDAG.equations (compile q).forest)).2 := by
      intro h
      exact hn ((holds_raw (compile q) ρ).mpr (ha.2.1.mp h))
    have hp := ha.1
    omega

theorem satisfiable {Γ} (q : Plan Γ) :
    (∃ ρ, Eval ρ q) ↔ ∃ ν, (compile q).Holds ν := by
  constructor
  · rintro ⟨ρ,hρ⟩
    obtain ⟨ν,_,hν⟩ := (compilation Γ q ρ).mp hρ
    exact ⟨ν,hν⟩
  · rintro ⟨ν,hν⟩
    refine ⟨fun x => ν ((compile q).embedding x),?_⟩
    exact (compilation Γ q _).mpr ⟨ν,fun _ => rfl,hν⟩

theorem strict_unsat {Γ} (q : Plan Γ) :
    Strict (strictPair q).1.term (strictPair q).2.term ↔ ¬ ∃ ρ, Eval ρ q := by
  apply Iff.trans ?_ (not_congr (satisfiable q)).symm
  constructor
  · intro hs he
    obtain ⟨ρ,hρ⟩ := he
    exact ((strict_at q ρ).mp (hs ρ)) hρ
  · intro hn ρ
    exact (strict_at q ρ).mpr (fun h => hn ⟨ρ,h⟩)

theorem weak_unsat {Γ} (q : Plan Γ) (hΓ : ∀ σ ∈ (compile q).context, σ=Ty.ground) :
    Weak (weakPair q).1.term (weakPair q).2.term ↔ ¬ ∃ ρ, Eval ρ q := by
  have hh := (GroundEquivalence.Proof.fullGroundEquivalence.2.1 (compile q).context hΓ
    (strictPair q).1.term (strictPair q).2.term).2
  change Weak (upperInput (strictPair q).1).term (lowerInput (strictPair q).2).term ↔ _
  rw [GroundEquivalence.Proof.upper_input,GroundEquivalence.Proof.lower_input]
  exact hh.symm.trans (strict_unsat q)
end LogicLineages.OrdinalComparison.Source.ExistentialPlan.Proof
