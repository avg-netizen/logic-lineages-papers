module
public import LogicLineages.OrdinalComparison.WWSourceFinitePositiveTargets
public import LogicLineages.OrdinalComparison.WWSourceAssignmentProfileProof
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentProof
public import LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceClasses
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof
open AdmissibleSum AdmissibleAssignment

theorem finitePositiveValueSound : Targets.FinitePositiveValueSound := by
  intro Γ t n hs
  induction t generalizing n with
  | var c => simp [finitePositiveValue] at hs
  | zero => simp [finitePositiveValue] at hs
  | omega => simp [finitePositiveValue] at hs
  | collapse f g ihf ihg => simp [finitePositiveValue] at hs
  | one =>
    have he : 1 = n := Option.some.inj hs
    subst n
    exact ⟨by omega, fun _ => by simp [denote]⟩
  | add f g ihf ihg =>
    obtain ⟨a, ha, b, hb, he⟩ : ∃ a, finitePositiveValue f = some a ∧
        ∃ b, finitePositiveValue g = some b ∧ a + b = n := by
      simpa only [finitePositiveValue, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using hs
    subst n
    obtain ⟨hpa, hva⟩ := ihf a ha
    obtain ⟨hpb, hvb⟩ := ihg b hb
    refine ⟨by omega, fun ρ => ?_⟩
    simp only [denote, hva ρ, hvb ρ]
    exact naturalSum_finite a b
  | emul f g ihf ihg =>
    obtain ⟨a, ha, b, hb, he⟩ : ∃ a, finitePositiveValue f = some a ∧
        ∃ b, finitePositiveValue g = some b ∧ 2 ^ a * b = n := by
      simpa only [finitePositiveValue, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using hs
    subst n
    obtain ⟨hpa, hva⟩ := ihf a ha
    obtain ⟨hpb, hvb⟩ := ihg b hb
    refine ⟨Nat.mul_pos (Nat.pow_pos (by omega)) hpb, fun ρ => ?_⟩
    simp only [denote, hva ρ, hvb ρ]
    rw [(finiteArithmetic a 0).2.2]
    exact naturalProduct_finite _ _

theorem generatedNoOmegaFinitePositive : Targets.GeneratedNoOmegaFinitePositive := by
  intro Γ i t hg
  induction hg with
  | one i => intro _ _ _; exact ⟨1, rfl⟩
  | omega i hi => intro _ _ hn; simp [noOmega] at hn
  | var x j => intro _ hc _; simp [ordinalExpressionVariables] at hc
  | add hf hg ihf ihg =>
    intro hi hc hn
    have hp := List.append_eq_nil_iff.mp hc
    have hn' := hn
    simp only [noOmega, Bool.and_eq_true_iff] at hn'
    obtain ⟨a, ha⟩ := ihf hi hp.1 hn'.1
    obtain ⟨b, hb⟩ := ihg hi hp.2 hn'.2
    exact ⟨a+b, by simp [finitePositiveValue, ha, hb]⟩
  | emul hi hf hg ihf ihg =>
    intro _ hc hn
    have hp := List.append_eq_nil_iff.mp hc
    have hn' := hn
    simp only [noOmega, Bool.and_eq_true_iff] at hn'
    obtain ⟨a, ha⟩ := ihf (by omega) hp.1 hn'.1
    obtain ⟨b, hb⟩ := ihg hi hp.2 hn'.2
    exact ⟨2^a*b, by simp [finitePositiveValue, ha, hb]⟩
  | collapse hf hg ihf ihg => intro hi _ _; omega

theorem actualRecursorFreePositiveFinite : Targets.ActualRecursorFreePositiveFinite := by
  intro Γ hΓ τ p t ht
  obtain ⟨v, hv, hg⟩ := actualAdmissibleAssignmentGenerated Γ τ p t
  obtain ⟨w, hw, hn⟩ := actualRecursorFreeAssignmentNoOmega Γ τ p t ht
  have he : w = v := Option.some.inj (hw.symm.trans hv)
  subst w
  refine ⟨v, hv, fun j hj => ?_⟩
  have hc := actualGeneratedGroundPositiveClosed Γ hΓ j.val (v j) hj (hg j)
  obtain ⟨n, hnv⟩ := generatedNoOmegaFinitePositive Γ j.val (v j) (hg j) hj hc (hn j)
  obtain ⟨hp, heq⟩ := finitePositiveValueSound Γ (v j) n hnv
  exact ⟨n, hp, hnv, heq⟩
end LogicLineages.OrdinalComparison.Source.SourceClasses
