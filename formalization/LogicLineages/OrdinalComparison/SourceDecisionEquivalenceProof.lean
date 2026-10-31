module
public import LogicLineages.OrdinalComparison.SourceDecisionEquivalenceCounterProof
public import LogicLineages.OrdinalComparison.SourceGroundArithmeticCounterProof
public import LogicLineages.OrdinalComparison.SourceBooleanCompilerProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.DecisionEquivalence.Proof
open GroundEquivalence

theorem universal_unsat {Γ τ υ} (hΓ : ∀ σ ∈ Γ, σ=Ty.ground) (strict : Bool)
    (a : Input Γ τ) (b : Input Γ υ) :
    Universal strict a b ↔ ¬ ∃ ρ, ExistentialPlan.Eval ρ (realize hΓ strict a b) := by
  classical
  constructor
  · intro hu he
    obtain ⟨ρ,hρ⟩ := he
    exact ((counter_correct Γ τ υ hΓ strict a b ρ).mp hρ) (hu ρ)
  · intro hn ρ
    by_contra h
    exact hn ⟨ρ,(counter_correct Γ τ υ hΓ strict a b ρ).mpr h⟩

theorem fullDecisionEquivalence : Targets.FullDecisionEquivalence := by
  classical
  refine ⟨numeric_effective,counter_correct,?_,?_,?_⟩
  · intro Γ τ υ hΓ strict a b
    have hs := ExistentialPlan.Proof.size Γ (realize hΓ strict a b)
    have hc := ExistentialPlan.Proof.comparison Γ hΓ (realize hΓ strict a b)
    have hu := universal_unsat hΓ strict a b
    have hstrict : Universal strict a b ↔
        Strict (toStrict hΓ strict a b).left.term (toStrict hΓ strict a b).right.term :=
      hu.trans hc.1.symm
    have hweak : Universal strict a b ↔
        Weak (toWeak hΓ strict a b).left.term (toWeak hΓ strict a b).right.term :=
      hu.trans hc.2.1.symm
    refine ⟨hs.2.2.2 hΓ,hs.2.2.2 hΓ,hstrict,hweak,?_⟩
    have ha := GroundArithmeticCounter.Proof.unsatisfiable (toStrict hΓ strict a b).context true
      (toStrict hΓ strict a b).left (toStrict hΓ strict a b).right
    exact hstrict.trans ha.symm
  · intro Γ hΓ strict a b
    have hh : Universal strict a b ↔ ∀ ρ, GroundArithmeticCounter.RawQuery strict ρ a b :=
      forall_congr' (fun ρ => GroundArithmeticCounter.Proof.groundQuery Γ ρ strict a b)
    cases strict <;> exact hh
  · intro Γ hΓ p
    have hc := BooleanCompiler.Proof.fullSourceBooleanCompiler.2.2.2 Γ hΓ p
    refine ⟨hc.2.2.1,hc.1.symm,hc.2.1.symm,?_⟩
    simpa only [not_not] using (not_congr hc.1).symm
end LogicLineages.OrdinalComparison.Source.DecisionEquivalence.Proof
