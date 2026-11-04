module
public import LogicLineages.OrdinalComparison.SourceGammaCollisionGrowthProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaCollision.Proof
theorem numeric_strict (b p q : Nat) (hne : p ≠ q) : rightValue b p q + 2 ≤ leftValue b p q := by
  let A := g b (3*p+p+2)
  let B := g b (3*q+q+2)
  let C := g b (3*p+q+2)
  let D := g b (3*q+p+2)
  have hw : 3*C+D < 3*A+B := by
    rcases lt_or_gt_of_ne hne with hpq | hqp
    · have hBD := g_four_lt b (3*q+p+2) (3*q+q+2) (by omega)
      have hCD := (g_strictMono b).monotone (show 3*p+q+2 ≤ 3*q+p+2 by omega)
      change 4*D < B at hBD
      change C ≤ D at hCD
      omega
    · have hAC := g_four_lt b (3*p+q+2) (3*p+p+2) (by omega)
      have hDC := (g_strictMono b).monotone (show 3*q+p+2 ≤ 3*p+q+2 by omega)
      change 4*C < A at hAC
      change D ≤ C at hDC
      omega
  have ho := g_four_lt b (3*C+D+2) (3*A+B+2) (by omega)
  have hp := g_positive b (3*C+D+2)
  change g b (3*C+D+2) + 2 ≤ g b (3*A+B+2)
  omega

theorem numeric_collision (b p q : Nat) :
    rightValue b p q ≤ leftValue b p q ∧
    (leftValue b p q = rightValue b p q ↔ p = q) ∧
    (p ≠ q → 2 ≤ leftValue b p q - rightValue b p q) := by
  by_cases he : p = q
  · subst q
    exact ⟨le_rfl, ⟨fun _ => rfl, fun _ => rfl⟩, fun h => False.elim (h rfl)⟩
  · have hs := numeric_strict b p q he
    refine ⟨by omega, ?_, fun _ => by omega⟩
    constructor
    · intro h
      omega
    · intro h
      exact False.elim (he h)

theorem numericCollision : Targets.NumericCollision := numeric_collision
end LogicLineages.OrdinalComparison.Source.SourceGammaCollision.Proof
