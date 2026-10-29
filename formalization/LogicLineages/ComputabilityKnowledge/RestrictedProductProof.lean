module

public import LogicLineages.ComputabilityKnowledge.Comparators.RestrictedProduct

@[expose] public section

/-!
# Proof of paper 02's bounded multiplication identity (`lem:restricted-product`)

Proves `Comparators.RestrictedProduct.Target` exactly as frozen. Write
`2^a = D + 1`. The argument follows the paper: Euclidean division of `s` by `a`,
the Mersenne residue of `2^r - 1` with `2^r < 2^a`, the geometric sum
`geom D k = Σ_{j<k} (D+1)^j` with `(D+1)^k = D * geom D k + 1`, and its residue
`geom D k ≡ k (mod D)`. Only Lean core lemmas and `omega` are used.
-/

namespace LogicLineages.ComputabilityKnowledge.RestrictedProductProof

open LogicLineages.ComputabilityKnowledge.PositiveExpression
open LogicLineages.ComputabilityKnowledge.Comparators.RestrictedProduct

/-- Geometric sum `1 + (D+1) + ... + (D+1)^(k-1)`. -/
def geom (D : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => (D + 1) * geom D k + 1

theorem pow_eq_geom (D k : Nat) : (D + 1) ^ k = D * geom D k + 1 := by
  induction k with
  | zero => simp [geom]
  | succ k ih =>
      have e0 : geom D (k + 1) = (D + 1) * geom D k + 1 := rfl
      have e1 : (D * geom D k + 1) * (D + 1) = D * geom D k * (D + 1) + (D + 1) := by
        rw [Nat.add_mul, Nat.one_mul]
      have e2 : D * ((D + 1) * geom D k + 1) = D * ((D + 1) * geom D k) + D := by
        rw [Nat.mul_add, Nat.mul_one]
      have e3 : D * ((D + 1) * geom D k) = D * geom D k * (D + 1) := by
        rw [Nat.mul_comm (D + 1) (geom D k), Nat.mul_assoc]
      rw [Nat.pow_succ, ih, e0]
      omega

theorem geom_mod (D k : Nat) : ∃ c, geom D k = k + D * c := by
  induction k with
  | zero => exact ⟨0, by simp [geom]⟩
  | succ k ih =>
      obtain ⟨c, hc⟩ := ih
      refine ⟨k + D * c + c, ?_⟩
      have e0 : geom D (k + 1) = (D + 1) * geom D k + 1 := rfl
      have f1 : (D + 1) * (k + D * c) = D * (k + D * c) + (k + D * c) := by
        rw [Nat.add_mul, Nat.one_mul]
      have f2 : D * (k + D * c + c) = D * (k + D * c) + D * c :=
        Nat.mul_add D (k + D * c) c
      rw [e0, hc]
      omega

/-- Uniqueness of the least residue modulo `D`. -/
theorem modUnique {D q p y k : Nat} (hy : y < D) (hk : k < D)
    (h : D * q + y = D * p + k) : y = k := by
  rcases Nat.lt_or_ge q p with hqp | hqp
  · obtain ⟨t, rfl⟩ : ∃ t, p = q + t + 1 := ⟨p - q - 1, by omega⟩
    have e : D * (q + t + 1) = D * q + D * t + D := by
      rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
    omega
  · rcases Nat.eq_or_lt_of_le hqp with he | hlt
    · subst he
      omega
    · obtain ⟨t, rfl⟩ : ∃ t, q = p + t + 1 := ⟨q - p - 1, by omega⟩
      have e : D * (p + t + 1) = D * p + D * t + D := by
        rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
      omega

theorem boundedMultiplication :
    LogicLineages.ComputabilityKnowledge.Comparators.RestrictedProduct.Target := by
  rintro ⟨A, hA⟩ ⟨Y, hY⟩ ⟨S, hS⟩ hy hs
  dsimp only at hy hs ⊢
  obtain ⟨D, hD⟩ : ∃ D, 2 ^ A = D + 1 :=
    ⟨2 ^ A - 1, by have := Nat.two_pow_pos A; omega⟩
  have hsub : 2 ^ A - 1 = D := by omega
  rw [hsub] at hy hs
  have hDpos : 0 < D := by omega
  constructor
  · -- s = a*y gives the witnesses u = geom D y, q = c + 1
    intro hsa
    obtain ⟨c, hc⟩ := geom_mod D Y
    have hu : 0 < geom D Y := by omega
    refine ⟨⟨geom D Y, hu⟩, ⟨c + 1, Nat.succ_pos c⟩, ?_, ?_⟩
    · show 2 ^ A * geom D Y + 1 = geom D Y + 2 ^ S
      have h1 : 2 ^ S = D * geom D Y + 1 := by
        rw [hsa, Nat.pow_mul, hD, pow_eq_geom]
      have h2 : 2 ^ A * geom D Y = D * geom D Y + geom D Y := by
        rw [hD, Nat.add_mul, Nat.one_mul]
      omega
    · show 2 ^ A * (c + 1) + Y + 1 = geom D Y + (c + 1) + 2 ^ A
      have h3 : 2 ^ A * (c + 1) = D * c + D + (c + 1) := by
        rw [hD, Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one]
      omega
  · -- the two equations force s = a*y
    rintro ⟨⟨U, hU⟩, ⟨Q, hQ⟩, e1, e2⟩
    have e1' : 2 ^ A * U + 1 = U + 2 ^ S := e1
    have e2' : 2 ^ A * Q + Y + 1 = U + Q + 2 ^ A := e2
    obtain ⟨k, r, hdec, hr⟩ : ∃ k r, A * k + r = S ∧ r < A :=
      ⟨S / A, S % A, Nat.div_add_mod S A, Nat.mod_lt S hA⟩
    have h2S : 2 ^ S = (D + 1) ^ k * 2 ^ r := by
      rw [← hdec, Nat.pow_add, Nat.pow_mul, hD]
    rw [pow_eq_geom D k] at h2S
    have f1 : (D * geom D k + 1) * 2 ^ r = D * (geom D k * 2 ^ r) + 2 ^ r := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
    have f2 : 2 ^ A * U = D * U + U := by
      rw [hD, Nat.add_mul, Nat.one_mul]
    have hpos : 0 < 2 ^ r := Nat.two_pow_pos r
    have hlt : 2 ^ (r + 1) ≤ 2 ^ A := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.pow_succ] at hlt
    have hmod : D * U + 0 = D * (geom D k * 2 ^ r) + (2 ^ r - 1) := by omega
    have hx := modUnique hDpos (by omega) hmod
    have h2r : 2 ^ r = 1 := by omega
    have hr0 : r = 0 := by
      rcases Nat.eq_zero_or_pos r with h | h
      · exact h
      · have h2 : 2 ^ 1 ≤ 2 ^ r := Nat.pow_le_pow_right (by decide) (by omega)
        rw [Nat.pow_one] at h2
        omega
    have hUg : U = geom D k := by
      apply Nat.eq_of_mul_eq_mul_left hDpos
      have hg : geom D k * 2 ^ r = geom D k := by rw [h2r, Nat.mul_one]
      rw [hg] at hmod
      omega
    obtain ⟨c, hc⟩ := geom_mod D k
    have hkD : k < D := by
      rcases Nat.lt_or_ge k D with h | h
      · exact h
      · have hmul : A * D ≤ A * k := Nat.mul_le_mul (Nat.le_refl A) h
        omega
    have fQ : 2 ^ A * Q = D * Q + Q := by
      rw [hD, Nat.add_mul, Nat.one_mul]
    have fc : D * (c + 1) = D * c + D := by
      rw [Nat.mul_add, Nat.mul_one]
    have hmod2 : D * Q + Y = D * (c + 1) + k := by omega
    have hYk := modUnique hy hkD hmod2
    subst hYk
    omega

end LogicLineages.ComputabilityKnowledge.RestrictedProductProof
