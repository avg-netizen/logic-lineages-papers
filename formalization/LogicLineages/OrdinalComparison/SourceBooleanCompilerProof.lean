module
public import LogicLineages.OrdinalComparison.SourceBooleanCompilerLowerProof
public import LogicLineages.OrdinalComparison.SourceBooleanCompilerSizeProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.BooleanCompiler.Proof
open GroundEquivalence

theorem fullSourceBooleanCompiler : Targets.FullSourceBooleanCompiler := by
  refine ⟨sourceObservations,lower_correct,?_,?_⟩
  · intro Γ p
    exact ⟨load_bound Γ p,lower_size Γ p⟩
  · intro Γ hΓ p
    have hc := ExistentialPlan.Proof.comparison Γ hΓ (lower p)
    have hs := ExistentialPlan.Proof.size Γ (lower p)
    have he : (∃ ρ, Eval ρ p) ↔ ∃ ρ, ExistentialPlan.Eval ρ (lower p) :=
      exists_congr (lower_correct Γ p)
    have hl := load_bound Γ p
    have hb := lower_size Γ p
    have hm : 1000*p.load ≤ 1000*(p.codeSize*(p.sourceMax+1)) := Nat.mul_le_mul_left 1000 hl
    have hv := hb.1.trans hm
    have hq := hb.2.1.trans hm
    have hw := hb.2.2.trans hm
    refine ⟨hc.1.trans (not_congr he).symm,hc.2.1.trans (not_congr he).symm,
      hs.2.2.2 hΓ,?_,?_,?_,?_,?_⟩
    · simp only [Nat.mul_assoc]
      omega
    · change (ExistentialPlan.strictPair (lower p)).1.specs.length ≤ _
      unfold budget
      simp only [Nat.mul_assoc]
      have hh := hc.2.2.1
      omega
    · change (ExistentialPlan.strictPair (lower p)).2.specs.length ≤ _
      unfold budget
      simp only [Nat.mul_assoc]
      have hh := hc.2.2.2.1
      omega
    · change (ExistentialPlan.weakPair (lower p)).1.specs.length ≤ _
      unfold budget
      simp only [Nat.mul_assoc]
      have hh := hc.2.2.2.2.1
      omega
    · change (ExistentialPlan.weakPair (lower p)).2.specs.length ≤ _
      unfold budget
      simp only [Nat.mul_assoc]
      have hh := hc.2.2.2.2.2
      omega
end LogicLineages.OrdinalComparison.Source.BooleanCompiler.Proof
