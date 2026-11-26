module
public import LogicLineages.CartierObserverCurrent.MixedWordTargets
public import LogicLineages.CartierObserverCurrent.MixedProperProof
public import LogicLineages.CartierObserverCurrent.PoleContractionProof
public meta import LogicLineages.Audit

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.MixedWord

theorem wordProper : Targets.WordProper.{u} := by
  intro K _ _ _ w
  induction w with
  | nil => intro f hf; exact hf
  | cons b w ih =>
    intro f hf
    exact ih _ (MixedProper.stepProper K b f hf)

theorem wordOrderBound : Targets.WordOrderBound.{u} := by
  intro K _ _ _ w
  induction w with
  | nil => intro f z M h; simpa only [execute, List.length_nil, pow_zero, mul_one] using h
  | cons b w ih =>
    intro f z M h
    apply ih (MixedProper.step b f) z M
    have hs := PoleContraction.canonicalPoleContraction K f b z
    have hp : M * 2 ^ (b :: w).length = 2 * (M * 2 ^ w.length) := by
      rw [List.length_cons, pow_succ]
      ring
    rw [hp] at h
    omega

theorem wordNoNewPole : Targets.WordNoNewPole.{u} := by
  intro K _ _ _ w f z h
  have hb := wordOrderBound K w f z 0 (by simp [h])
  exact Nat.eq_zero_of_le_zero hb

#audit_namespace LogicLineages.CartierObserverCurrent.MixedWord
end LogicLineages.CartierObserverCurrent.MixedWord
