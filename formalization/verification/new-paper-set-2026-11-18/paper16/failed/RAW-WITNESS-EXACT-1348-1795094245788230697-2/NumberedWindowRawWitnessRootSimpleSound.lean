import LogicLineages.PersistentMarking.NumberedWindowRawWitnessLaws

namespace LogicLineages.PersistentMarking.NumberedWindowRawWitnessRootSimpleSound
open Spine NumberedWindowSyntax NumberedWindowRules NumberedWindowLiteralEquality
open NumberedWindowRawWitnessRootBits NumberedWindowRawWitnessLaws

theorem mark {S K k Q R} (h : rootBit S K (.mark k) Q R = true) :
    RawStep S K Q R := by
  cases Q <;> try (simp only [rootBit,Bool.false_eq_true] at h)
  case ordinary f bs =>
    have e : NTerm.numbered f f.result k bs .nil = R := (termEqTrue _ _).mp h
    rw [← e]
    exact .mark

theorem lower {S K Q R} (h : rootBit S K .lower Q R = true) : RawStep S K Q R := by
  cases Q <;> try (simp only [rootBit,Bool.false_eq_true] at h)
  case numbered f τ k bs es =>
    cases k with
    | zero => simp only [rootBit,Bool.false_eq_true] at h
    | succ k =>
      have e : NTerm.numbered f τ k bs es = R := (termEqTrue _ _).mp h
      rw [← e]
      exact .lower

theorem fabs {S K Q R} (h : rootBit S K .fabs Q R = true) : RawStep S K Q R := by
  cases Q <;> try (simp only [rootBit,Bool.false_eq_true] at h)
  case numbered f τ k bs es =>
    cases τ with
    | ground => simp only [rootBit,Bool.false_eq_true] at h
    | arrow σ τ =>
      cases k with
      | zero => simp only [rootBit,Bool.false_eq_true] at h
      | succ k =>
        have e : NTerm.lam σ (openNumbered f σ τ k bs es) = R := (termEqTrue _ _).mp h
        rw [← e]
        exact .fabs

theorem beta {S K Q R} (h : rootBit S K .beta Q R = true) : RawStep S K Q R := by
  cases Q <;> try (simp only [rootBit,Bool.false_eq_true] at h)
  case auxApp σ τ q a =>
    cases q <;> try (simp only [rootBit,Bool.false_eq_true] at h)
    case lam ρ b =>
      change (decide (σ = ρ) && termEq (substitute (.cons a .nil) 0 b) R) = true at h
      obtain ⟨hσ,e⟩ := Bool.and_eq_true_iff.mp h
      have hd : σ = ρ := of_decide_eq_true hσ
      subst ρ
      have he : substitute (.cons a .nil) 0 b = R := (termEqTrue _ _).mp e
      rw [← he]
      exact .beta

theorem bottom {S K Q R} (h : rootBit S K .bottom Q R = true) : RawStep S K Q R := by
  change (!termEq Q (.bottom Q.type) && termEq (.bottom Q.type) R) = true at h
  simp only [Bool.and_eq_true,Bool.not_eq_true',Bool.eq_false_iff,termEqTrue] at h
  obtain ⟨hn,e⟩ := h
  rw [← e]
  exact .bottom hn

end LogicLineages.PersistentMarking.NumberedWindowRawWitnessRootSimpleSound
