module
public import LogicLineages.ControlSensitivityCurrent.FullCollisionTargets
public import LogicLineages.ControlSensitivityCurrent.FullAdditionProof
public import LogicLineages.OrdinalComparison.ElementaryControl
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PolicyCollision
open LogicLineages.OrdinalComparison
private theorem g_positive (f : Nat → Nat) (n : Nat) : 0 < g f n := by unfold g; omega
private theorem g_strictMono (f : Nat → Nat) (hf : FullAddition.Targets.SourceGrowth f) : StrictMono (g f) := by
  have hm := (FullAddition.completeAddition.2.2.2 f hf).1
  intro a b hab
  have h := hm (show a+2 < b+2 by omega)
  unfold g
  omega
private theorem g_four_gap (f : Nat → Nat) (hf : FullAddition.Targets.SourceGrowth f) (n : Nat) :
    4*g f n < g f (n+1) := by
  have ha : 4 ≤ f (n+2) := (four_le_Phi _).trans (hf.1 _)
  have h := four_mul_add_four_lt_two_pow_succ ha
  have he : f (n+2)+1 ≤ 2^f (n+2) := (f (n+2)).lt_two_pow_self
  have hh := h.trans_le (Nat.pow_le_pow_right (by decide) he)
  have hg := hf.2 (n+2)
  have hn : n+2+1 = n+1+2 := by omega
  rw [hn] at hg
  unfold g
  omega
private theorem g_four_lt (f : Nat → Nat) (hf : FullAddition.Targets.SourceGrowth f)
    (a b : Nat) (hab : a < b) : 4*g f a < g f b :=
  (g_four_gap f hf a).trans_le ((g_strictMono f hf).monotone (Nat.succ_le_of_lt hab))
theorem numeric_strict (f : Nat → Nat) (hf : FullAddition.Targets.SourceGrowth f) (p q : Nat) (hne : p ≠ q) : rightValue f p q + 2 ≤ leftValue f p q := by
  let A := g f (3*p+p+2)
  let B := g f (3*q+q+2)
  let C := g f (3*p+q+2)
  let D := g f (3*q+p+2)
  have hw : 3*C+D < 3*A+B := by
    rcases lt_or_gt_of_ne hne with hpq | hqp
    · have hBD := g_four_lt f hf (3*q+p+2) (3*q+q+2) (by omega)
      have hCD := (g_strictMono f hf).monotone (show 3*p+q+2 ≤ 3*q+p+2 by omega)
      change 4*D < B at hBD
      change C ≤ D at hCD
      omega
    · have hAC := g_four_lt f hf (3*p+q+2) (3*p+p+2) (by omega)
      have hDC := (g_strictMono f hf).monotone (show 3*q+p+2 ≤ 3*p+q+2 by omega)
      change 4*C < A at hAC
      change D ≤ C at hDC
      omega
  have ho := g_four_lt f hf (3*C+D+2) (3*A+B+2) (by omega)
  have hp := g_positive f (3*C+D+2)
  change g f (3*C+D+2) + 2 ≤ g f (3*A+B+2)
  omega

theorem numeric_collision (f : Nat → Nat) (hf : FullAddition.Targets.SourceGrowth f) (p q : Nat) :
    rightValue f p q ≤ leftValue f p q ∧
    (leftValue f p q = rightValue f p q ↔ p = q) ∧
    (p ≠ q → 2 ≤ leftValue f p q - rightValue f p q) := by
  by_cases he : p = q
  · subst q
    exact ⟨le_rfl, ⟨fun _ => rfl, fun _ => rfl⟩, fun h => False.elim (h rfl)⟩
  · have hs := numeric_strict f hf p q he
    refine ⟨by omega, ?_, fun _ => by omega⟩
    constructor
    · intro h
      omega
    · intro h
      exact False.elim (he h)


theorem numericCollision : FullCollision.Targets.NumericCollision := by
  intro f hf
  exact ⟨fun n => ⟨g_positive f n,g_four_gap f hf n⟩,numeric_collision f hf⟩
#audit_namespace LogicLineages.ControlSensitivityCurrent.PolicyCollision
end LogicLineages.ControlSensitivityCurrent.PolicyCollision
