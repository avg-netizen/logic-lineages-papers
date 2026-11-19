import LogicLineages.PersistentMarking.NumberedWindowRawWitnessLaws

namespace LogicLineages.PersistentMarking.NumberedWindowRawWitnessContextSimpleSound
open Spine NumberedWindowSyntax NumberedWindowRules NumberedWindowLiteralEquality
open NumberedWindowRawWitnessBits NumberedWindowRawWitnessLaws

theorem argsAt {S K} {test : NTerm → NTerm → Bool}
    (sound : ∀ Q R, test Q R = true → RawStep S K Q R) :
    ∀ i qs rs, argsAtBit test i qs rs = true → RawArgsStep S K qs rs := by
  intro i
  induction i with
  | zero =>
    intro qs rs h
    cases qs with
    | nil => cases rs <;> simp only [argsAtBit,Bool.false_eq_true] at h
    | cons Q qs =>
      cases rs with
      | nil => simp only [argsAtBit,Bool.false_eq_true] at h
      | cons R rs =>
        change (test Q R && argsEq qs rs) = true at h
        obtain ⟨hQR,eq⟩ := Bool.and_eq_true_iff.mp h
        have he : qs = rs := (argsEqTrue _ _).mp eq
        subst rs
        exact .first (sound _ _ hQR)
  | succ i ih =>
    intro qs rs h
    cases qs with
    | nil => cases rs <;> simp only [argsAtBit,Bool.false_eq_true] at h
    | cons Q qs =>
      cases rs with
      | nil => simp only [argsAtBit,Bool.false_eq_true] at h
      | cons R rs =>
        change (termEq Q R && argsAtBit test i qs rs) = true at h
        obtain ⟨eq,ht⟩ := Bool.and_eq_true_iff.mp h
        have he : Q = R := (termEqTrue _ _).mp eq
        subst R
        exact .later (ih _ _ ht)

theorem lam {S K w} (ih : ∀ Q R, rawBit S K w Q R = true → RawStep S K Q R) :
    ∀ Q R, rawBit S K (.lam w) Q R = true → RawStep S K Q R := by
  intro Q R h
  cases Q <;> try (simp only [rawBit,Bool.false_eq_true] at h)
  case lam σ Q =>
    cases R <;> try (simp only [rawBit,Bool.false_eq_true] at h)
    case lam ρ R =>
      change (decide (σ = ρ) && rawBit S K w Q R) = true at h
      obtain ⟨ed,hQR⟩ := Bool.and_eq_true_iff.mp h
      have he : σ = ρ := of_decide_eq_true ed
      subst ρ
      exact .lam (ih _ _ hQR)

theorem ordinaryBase {S K i w}
    (ih : ∀ Q R, rawBit S K w Q R = true → RawStep S K Q R) :
    ∀ Q R, rawBit S K (.ordinaryBase i w) Q R = true → RawStep S K Q R := by
  intro Q R h
  cases Q <;> try (simp only [rawBit,Bool.false_eq_true] at h)
  case ordinary f qs =>
    cases R <;> try (simp only [rawBit,Bool.false_eq_true] at h)
    case ordinary g rs =>
      change (decide (f = g) && argsAtBit (rawBit S K w) i qs rs) = true at h
      obtain ⟨ed,ha⟩ := Bool.and_eq_true_iff.mp h
      have he : f = g := of_decide_eq_true ed
      subst g
      exact .ordinaryBase (argsAt ih i _ _ ha)

theorem auxFunction {S K w}
    (ih : ∀ Q R, rawBit S K w Q R = true → RawStep S K Q R) :
    ∀ Q R, rawBit S K (.auxFunction w) Q R = true → RawStep S K Q R := by
  intro Q R h
  cases Q <;> try (simp only [rawBit,Bool.false_eq_true] at h)
  case auxApp σ τ Q A =>
    cases R <;> try (simp only [rawBit,Bool.false_eq_true] at h)
    case auxApp ρ υ R B =>
      change (decide (σ = ρ) && decide (τ = υ) && termEq A B &&
        rawBit S K w Q R) = true at h
      simp only [Bool.and_eq_true,decide_eq_true_eq,termEqTrue] at h
      rcases h with ⟨⟨⟨es,et⟩,ea⟩,hq⟩
      subst ρ
      subst υ
      subst B
      exact .auxFunction (ih _ _ hq)

end LogicLineages.PersistentMarking.NumberedWindowRawWitnessContextSimpleSound
