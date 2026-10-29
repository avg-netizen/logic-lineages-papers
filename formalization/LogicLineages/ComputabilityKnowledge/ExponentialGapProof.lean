module

public import LogicLineages.ComputabilityKnowledge.Comparators.ExponentialGap
public import Mathlib.Data.Nat.Basic

@[expose] public section


/-!
# Proof of the paper-02 finite-system collision comparator

Proves `Comparators.ExponentialGap.Target` exactly as frozen: for every finite
system of equations, the literal right term V is at most the literal left term
U, with equality exactly when every equation holds. The empty system is
included. The arithmetic core is the square identity
`x*x + y*y = x*y*2 + k*k` for `x = 2^a`, `y = 2^b`, written in ℕ with an
explicit nonnegative difference `k`.
-/

namespace LogicLineages.ComputabilityKnowledge.ExponentialGapProof

open LogicLineages.ComputabilityKnowledge.PositiveExpression
open LogicLineages.ComputabilityKnowledge.Comparators.ExponentialGap

/-- Two-variable square inequality with its equality case, in ℕ. -/
theorem sqGap (x y : Nat) :
    x * y * 2 ≤ x * x + y * y ∧ (x * x + y * y = x * y * 2 → x = y) := by
  rcases Nat.le_total x y with h | h
  · obtain ⟨k, rfl⟩ : ∃ k, y = x + k := ⟨y - x, by omega⟩
    have h1 : (x + k) * (x + k) = x * (x + k) + k * (x + k) := Nat.add_mul x k (x + k)
    have h2 : x * (x + k) = x * x + x * k := Nat.mul_add x x k
    have h3 : k * (x + k) = k * x + k * k := Nat.mul_add k x k
    have h4 : k * x = x * k := Nat.mul_comm k x
    refine ⟨by omega, fun heq => ?_⟩
    have hk : k * k = 0 := by omega
    rcases Nat.mul_eq_zero.mp hk with h0 | h0 <;> omega
  · obtain ⟨k, rfl⟩ : ∃ k, x = y + k := ⟨x - y, by omega⟩
    have h1 : (y + k) * (y + k) = y * (y + k) + k * (y + k) := Nat.add_mul y k (y + k)
    have h2 : y * (y + k) = y * y + y * k := Nat.mul_add y y k
    have h3 : k * (y + k) = k * y + k * k := Nat.mul_add k y k
    have h4 : k * y = y * k := Nat.mul_comm k y
    have h5 : (y + k) * y = y * y + k * y := Nat.add_mul y k y
    refine ⟨by omega, fun heq => ?_⟩
    have hk : k * k = 0 := by omega
    rcases Nat.mul_eq_zero.mp hk with h0 | h0 <;> omega

theorem leftPair_eval {ι : Type} (ρ : ι → PosNat) (a b : Expr ι) :
    (leftPair a b).eval ρ
      = 2 ^ a.eval ρ * 2 ^ a.eval ρ + 2 ^ b.eval ρ * 2 ^ b.eval ρ := by
  simp only [leftPair, eval_add, eval_emul, eval_one, Nat.mul_one]
  rw [Nat.pow_add, Nat.pow_add]

theorem rightPair_eval {ι : Type} (ρ : ι → PosNat) (a b : Expr ι) :
    (rightPair a b).eval ρ = 2 ^ a.eval ρ * 2 ^ b.eval ρ * 2 := by
  simp only [rightPair, eval_add, eval_emul, eval_one, Nat.mul_one]
  rw [Nat.pow_succ, Nat.pow_add]

/-- One equation: the pair gadget is a collision detector. -/
theorem pairCollision {ι : Type} (ρ : ι → PosNat) (a b : Expr ι) :
    (rightPair a b).eval ρ ≤ (leftPair a b).eval ρ ∧
      ((leftPair a b).eval ρ = (rightPair a b).eval ρ ↔ a.eval ρ = b.eval ρ) := by
  rw [leftPair_eval, rightPair_eval]
  obtain ⟨hle, heq⟩ := sqGap (2 ^ a.eval ρ) (2 ^ b.eval ρ)
  refine ⟨hle, fun h => Nat.pow_right_injective (Nat.le_refl 2) (heq h), fun h => ?_⟩
  rw [h, Nat.mul_two]

theorem sumEq {p q r s : Nat} (h1 : q ≤ p) (h2 : s ≤ r) (h : p + r = q + s) :
    p = q ∧ r = s :=
  ⟨by omega, by omega⟩

theorem allEquations_cons {ι : Type} (ρ : ι → PosNat) (a b : Expr ι)
    (rest : List (Expr ι × Expr ι)) :
    AllEquations ρ ((a, b) :: rest) ↔ (a.eval ρ = b.eval ρ ∧ AllEquations ρ rest) := by
  constructor
  · intro h
    exact ⟨h (a, b) (List.Mem.head rest), fun q hq => h q (List.Mem.tail (a, b) hq)⟩
  · rintro ⟨h1, h2⟩ q hq
    rcases hq with _ | ⟨_, hq⟩
    · exact h1
    · exact h2 _ hq

/-- The whole finite system, by induction on the list. -/
theorem systemCollision {ι : Type} (ρ : ι → PosNat) :
    ∀ equations : List (Expr ι × Expr ι),
      (systemRight equations).eval ρ ≤ (systemLeft equations).eval ρ ∧
        ((systemLeft equations).eval ρ = (systemRight equations).eval ρ ↔
          AllEquations ρ equations) := by
  intro equations
  induction equations with
  | nil =>
      refine ⟨Nat.le_refl _, ⟨fun _ q hq => ?_, fun _ => rfl⟩⟩
      cases hq
  | cons head rest ih =>
      obtain ⟨a, b⟩ := head
      have hL : (systemLeft ((a, b) :: rest)).eval ρ
          = (leftPair a b).eval ρ + (systemLeft rest).eval ρ := rfl
      have hR : (systemRight ((a, b) :: rest)).eval ρ
          = (rightPair a b).eval ρ + (systemRight rest).eval ρ := rfl
      obtain ⟨p1, p2⟩ := pairCollision ρ a b
      obtain ⟨i1, i2⟩ := ih
      rw [hL, hR, allEquations_cons]
      refine ⟨Nat.add_le_add p1 i1, ⟨fun h => ?_, fun h => ?_⟩⟩
      · obtain ⟨e1, e2⟩ := sumEq p1 i1 h
        exact ⟨p2.mp e1, i2.mp e2⟩
      · rw [p2.mpr h.1, i2.mpr h.2]

theorem finiteSystemCollision :
    LogicLineages.ComputabilityKnowledge.Comparators.ExponentialGap.Target := by
  intro d equations ρ
  exact systemCollision ρ equations

end LogicLineages.ComputabilityKnowledge.ExponentialGapProof
