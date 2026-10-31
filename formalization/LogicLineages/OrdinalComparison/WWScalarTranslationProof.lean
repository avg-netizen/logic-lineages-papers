module
public import LogicLineages.OrdinalComparison.WWScalarTranslationTargets
public import LogicLineages.OrdinalComparison.WWClosedPositiveEvaluationProof
public import LogicLineages.OrdinalComparison.WWGeneratedSupportProof
public import LogicLineages.OrdinalComparison.WWFiniteNaturalTailProof
public import LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ForwardTranslation
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

theorem scalarTranslationSound : Targets.ScalarTranslationSound := by
  intro Γ t s hs
  induction t generalizing s with
  | var c =>
    have he : Scalar.var c = s := Option.some.inj hs
    subst s
    intro ρ
    rfl
  | zero => simp [compileScalar] at hs
  | one =>
    have he : Scalar.one = s := Option.some.inj hs
    subst s
    intro ρ
    simp [Scalar.value, denote]
  | omega => simp [compileScalar] at hs
  | add f g ihf ihg =>
    obtain ⟨a, ha, b, hb, he⟩ : ∃ a, compileScalar f = some a ∧
        ∃ b, compileScalar g = some b ∧ Scalar.add a b = s := by
      simpa only [compileScalar, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using hs
    subst s
    intro ρ
    change ((a.value ρ + b.value ρ : Nat) : Ordinal) =
      ordinalNaturalSum (denote (fun c => (ρ c : Ordinal)) f) (denote (fun c => (ρ c : Ordinal)) g)
    rw [← ihf a ha ρ, ← ihg b hb ρ, naturalSum_finite]
  | emul f g ihf ihg => simp [compileScalar] at hs
  | collapse f g ihf ihg =>
    obtain ⟨a, ha, b, hb, he⟩ : ∃ a, extractPositive f = some a ∧
        ∃ b, compileScalar g = some b ∧ Scalar.shift a b = s := by
      simpa only [compileScalar, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using hs
    subst s
    intro ρ
    change (actualCollapse (fixedHead a + (b.value ρ : Ordinal)) : Ordinal) =
      (actualCollapse (ordinalNaturalSum
        (ordinalNaturalProduct Ordinal.omega0 (denote (fun c => (ρ c : Ordinal)) f))
        (denote (fun c => (ρ c : Ordinal)) g)) : Ordinal)
    rw [← closedPositiveEvaluationSound Γ f a ha (fun c => (ρ c : Ordinal)),
      ← ihg b hb ρ, actualNaturalSumFiniteRight]
    rfl

private theorem generated_scalar_total {Γ : List Ty} (hΓ : ∀ τ ∈ Γ, τ = Ty.ground)
    {i : Nat} {t : OrdinalExpression Γ} (hg : GeneratedOrdinalGrade Γ i t) :
    i = 0 → ∃ s : Scalar (OrdinalComponent Γ), compileScalar t = some s := by
  induction hg with
  | one i => intro _; exact ⟨.one, rfl⟩
  | omega i hi => intro he; omega
  | var x j => intro _; exact ⟨.var _, rfl⟩
  | add hf hg ihf ihg =>
    intro he
    obtain ⟨a, ha⟩ := ihf he
    obtain ⟨b, hb⟩ := ihg he
    exact ⟨.add a b, by simp [compileScalar, ha, hb]⟩
  | emul hi hf hg ihf ihg => intro he; omega
  | @collapse f g hf hg ihf ihg =>
    intro _
    have hc := actualGeneratedGroundPositiveClosed Γ hΓ 1 f (by omega) hf
    obtain ⟨a, ha⟩ := generatedClosedPositiveEvaluationTotal Γ 1 f hf (by omega) hc
    obtain ⟨b, hb⟩ := ihg rfl
    exact ⟨.shift a b, by simp [compileScalar, ha, hb]⟩

theorem generatedGroundScalarTranslationTotal : Targets.GeneratedGroundScalarTranslationTotal := by
  intro Γ hΓ t hg
  exact generated_scalar_total hΓ hg rfl

end LogicLineages.OrdinalComparison.Source.ForwardTranslation
