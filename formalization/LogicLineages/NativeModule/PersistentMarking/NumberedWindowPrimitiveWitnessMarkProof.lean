module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPrimitiveWitnessTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowLiteralEqualityProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowPrimitiveWitnessMarkProof
open NumberedWindowSyntax NumberedWindowRules NumberedWindowLiteralEquality
open NumberedWindowPrimitiveWitnessBits NumberedWindowPrimitiveWitnessTargets

private theorem argsRefl (bs : NArgs) : argsEq bs bs = true :=
  (NumberedWindowLiteralEqualityProof.args bs bs).mpr rfl

private theorem sound : ∀ Q R, markBit Q R = true → MarkDecrease Q R := by
  intro Q
  induction Q using NTerm.rec (motive_2 := fun _ => True) with
  | free σ i =>
    intro R h
    cases R <;> simp only [markBit,Bool.false_eq_true] at h
  | bound σ i =>
    intro R h
    cases R <;> simp only [markBit,Bool.false_eq_true] at h
  | bottom σ =>
    intro R h
    cases R <;> simp only [markBit,Bool.false_eq_true] at h
  | auxApp σ τ Q A ihQ ihA =>
    intro R h
    cases R <;> simp only [markBit,Bool.false_eq_true] at h
  | lam σ Q ih =>
    intro R h
    cases R <;> try (simp only [markBit,Bool.false_eq_true] at h)
    case lam ρ R =>
      change (decide (σ = ρ) && markBit Q R) = true at h
      obtain ⟨e,hr⟩ := Bool.and_eq_true_iff.mp h
      have e' : σ = ρ := of_decide_eq_true e
      subst ρ
      exact .lam (ih R hr)
  | ordinary f bs ih =>
    intro R h
    cases R <;> try (simp only [markBit,Bool.false_eq_true] at h)
    case numbered g τ k bt et =>
      cases et with
      | nil =>
        simp only [markBit,Bool.and_eq_true,decide_eq_true_eq,
          NumberedWindowLiteralEqualityProof.args bs bt] at h
        rcases h with ⟨⟨ef,eτ⟩,eb⟩
        subst g
        subst τ
        subst bt
        exact .omega
      | cons a es => simp only [markBit,Bool.false_eq_true] at h
  | numbered f τ k bs es ihB ihE =>
    intro R h
    cases R <;> try (simp only [markBit,Bool.false_eq_true] at h)
    case numbered g ρ l bt et =>
      change (decide (f = g) && decide (τ = ρ) && decide (l < k) &&
        argsEq bs bt && argsEq es et) = true at h
      simp only [Bool.and_eq_true,decide_eq_true_eq,
        NumberedWindowLiteralEqualityProof.args bs bt,
        NumberedWindowLiteralEqualityProof.args es et] at h
      rcases h with ⟨⟨⟨⟨ef,eτ⟩,hl⟩,eb⟩,ee⟩
      subst g
      subst ρ
      subst bt
      subst et
      exact .finite hl
  | nil => trivial
  | cons q qs ihQ ihA => trivial

private theorem complete : ∀ Q R, MarkDecrease Q R → markBit Q R = true := by
  intro Q R h
  induction h with
  | omega => simp [markBit,argsRefl]
  | finite hl => simp [markBit,argsRefl,hl]
  | lam _ ih => simp [markBit,ih]

theorem reflection : ExactLiteralMarkBit :=
  fun Q R => ⟨sound Q R,complete Q R⟩

end LogicLineages.PersistentMarking.NumberedWindowPrimitiveWitnessMarkProof
