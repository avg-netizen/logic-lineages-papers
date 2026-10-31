module
public import LogicLineages.OrdinalComparison.SourceCollisionCompletionTargets
public import LogicLineages.OrdinalComparison.SourceAdditionCompletionArithmeticProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceCollisionCompletion.Proof

theorem g_calibration (n : Nat) : g n = Phi (n+2)+1 := by
  simpa [g, Nat.add_comm] using actualFiniteHeadCollapse 1 n

theorem g_positive (n : Nat) : 0 < g n := by
  rw [g_calibration]
  omega

theorem g_strictMono : StrictMono g := by
  intro a b hab
  rw [g_calibration, g_calibration]
  have := Phi_strictMono (show a+2 < b+2 by omega)
  omega

theorem g_four_gap (n : Nat) : 4 * g n < g (n+1) := by
  rw [g_calibration, g_calibration]
  have h := Phi_linear_gap (n+2)
  have he : n+1+2 = n+2+1 := by omega
  rw [he]
  omega

theorem g_four_lt (a b : Nat) (hab : a < b) : 4 * g a < g b :=
  (g_four_gap a).trans_le (g_strictMono.monotone (Nat.succ_le_of_lt hab))

noncomputable def leftValue (p q : Nat) : Nat := g (3 * g (3*p+p+2) + g (3*q+q+2) + 2)
noncomputable def rightValue (p q : Nat) : Nat := g (3 * g (3*p+q+2) + g (3*q+p+2) + 2)

theorem numeric_strict (p q : Nat) (hne : p ≠ q) : rightValue p q + 2 ≤ leftValue p q := by
  let A := g (3*p+p+2)
  let B := g (3*q+q+2)
  let C := g (3*p+q+2)
  let D := g (3*q+p+2)
  have hw : 3*C+D < 3*A+B := by
    rcases lt_or_gt_of_ne hne with hpq | hqp
    · have hBD := g_four_lt (3*q+p+2) (3*q+q+2) (by omega)
      have hCD := g_strictMono.monotone (show 3*p+q+2 ≤ 3*q+p+2 by omega)
      change 4*D < B at hBD
      change C ≤ D at hCD
      omega
    · have hAC := g_four_lt (3*p+q+2) (3*p+p+2) (by omega)
      have hDC := g_strictMono.monotone (show 3*q+p+2 ≤ 3*p+q+2 by omega)
      change 4*C < A at hAC
      change D ≤ C at hDC
      omega
  have ho := g_four_lt (3*C+D+2) (3*A+B+2) (by omega)
  have hp := g_positive (3*C+D+2)
  change g (3*C+D+2) + 2 ≤ g (3*A+B+2)
  omega

theorem numeric_collision (p q : Nat) :
    rightValue p q ≤ leftValue p q ∧
    (leftValue p q = rightValue p q ↔ p = q) ∧
    (p ≠ q → 2 ≤ leftValue p q - rightValue p q) := by
  by_cases he : p = q
  · subst q
    exact ⟨le_rfl, ⟨fun _ => rfl, fun _ => rfl⟩, fun h => False.elim (h rfl)⟩
  · have hs := numeric_strict p q he
    refine ⟨by omega, ?_, fun _ => by omega⟩
    constructor
    · intro h
      omega
    · intro h
      exact False.elim (he h)
end LogicLineages.OrdinalComparison.Source.SourceCollisionCompletion.Proof
