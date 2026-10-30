module
public import LogicLineages.OrdinalComparison.TotientBoundTargets
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace LogicLineages.OrdinalComparison

private theorem distinct_factor_product_bound (s : Finset Nat) (hs : ∀ p ∈ s, 2 ≤ p) :
    (∏ p ∈ s, p) ≤ (s.card + 1) * ∏ p ∈ s, (p - 1) := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s hmax ih =>
    have ha : a ∉ s := by intro ha; exact (Nat.lt_irrefl a) (hmax a ha)
    have ha2 : 2 ≤ a := hs a (Finset.mem_insert_self _ _)
    have hs2 : ∀ p ∈ s, 2 ≤ p := fun p hp => hs p (Finset.mem_insert_of_mem hp)
    have hcard : s.card ≤ a - 2 := by
      calc
        s.card ≤ (Finset.Ico 2 a).card := Finset.card_le_card (fun p hp =>
          Finset.mem_Ico.mpr ⟨hs2 p hp, hmax p hp⟩)
        _ = a - 2 := Nat.card_Ico 2 a
    have hnum : a * (s.card + 1) ≤ (s.card + 2) * (a - 1) := by
      have ha1 : a - 1 + 1 = a := Nat.sub_add_cancel (by omega)
      have hca : s.card + 2 ≤ a := by omega
      nlinarith
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    calc
      a * (∏ p ∈ s, p) ≤ a * ((s.card + 1) * ∏ p ∈ s, (p - 1)) :=
        Nat.mul_le_mul_left a (ih hs2)
      _ ≤ (s.card + 1 + 1) * ((a - 1) * ∏ p ∈ s, (p - 1)) := by
        simpa only [Nat.mul_assoc, Nat.add_assoc] using
          Nat.mul_le_mul_right (∏ p ∈ s, (p - 1)) hnum

theorem actualTotientPrimeFactorBound : Targets.ActualTotientPrimeFactorBound := by
  intro n hn
  have hbound := distinct_factor_product_bound n.primeFactors
    (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  have hpositive : 0 < ∏ p ∈ n.primeFactors, (p - 1) :=
    Finset.prod_pos (fun p hp => by have h := (Nat.prime_of_mem_primeFactors hp).two_le; omega)
  apply Nat.le_of_mul_le_mul_right _ hpositive
  calc
    n * (∏ p ∈ n.primeFactors, (p - 1)) = Nat.totient n * ∏ p ∈ n.primeFactors, p :=
      (Nat.totient_mul_prod_primeFactors n).symm
    _ ≤ Nat.totient n * ((n.primeFactors.card + 1) * ∏ p ∈ n.primeFactors, (p - 1)) :=
      Nat.mul_le_mul_left _ hbound
    _ = ((n.primeFactors.card + 1) * Nat.totient n) * ∏ p ∈ n.primeFactors, (p - 1) := by ring

theorem actualFermatShapeTotientLowerBound : Targets.ActualFermatShapeTotientLowerBound := by
  intro r hr
  have hqpos : 0 < 2 ^ r + 1 := Nat.succ_pos _
  have hpow : 2 ^ (2 ^ r + 1).primeFactors.card ≤ 2 ^ r + 1 := by
    calc
      2 ^ (2 ^ r + 1).primeFactors.card ≤ ∏ p ∈ (2 ^ r + 1).primeFactors, p :=
        Finset.pow_card_le_prod _ _ 2 (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
      _ ≤ 2 ^ r + 1 := Nat.le_of_dvd hqpos (Nat.prod_primeFactors_dvd _)
  have hlt : 2 ^ r + 1 < 2 ^ (r + 1) := by
    have hp : 1 < 2 ^ r := one_lt_pow₀ (by decide) hr.ne'
    rw [pow_succ]
    omega
  have hcard : (2 ^ r + 1).primeFactors.card ≤ r :=
    Nat.le_of_lt_succ ((Nat.pow_lt_pow_iff_right (by decide)).mp (hpow.trans_lt hlt))
  calc
    2 ^ r < 2 ^ r + 1 := Nat.lt_succ_self _
    _ ≤ ((2 ^ r + 1).primeFactors.card + 1) * Nat.totient (2 ^ r + 1) :=
      actualTotientPrimeFactorBound _ hqpos
    _ ≤ (r + 1) * Nat.totient (2 ^ r + 1) := Nat.mul_le_mul_right _ (Nat.add_le_add_right hcard 1)

end LogicLineages.OrdinalComparison
