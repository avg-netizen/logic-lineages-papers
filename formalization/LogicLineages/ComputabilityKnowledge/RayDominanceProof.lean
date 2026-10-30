module

public import LogicLineages.ComputabilityKnowledge.Comparators.RayDominance
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

/-! The elementary finite integer estimate used in source N3. No actual
normal-form key ordering or lower-contribution bound is assumed as solved.
-/
namespace LogicLineages.ComputabilityKnowledge.RayDominanceProof

open LogicLineages.ComputabilityKnowledge.RayDominance

theorem powerGrowth : Comparators.RayDominance.PowerGrowth := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => decide
  | succ t ht ih =>
    rw [Nat.pow_succ]
    nlinarith

theorem lowerContribution : Comparators.RayDominance.LowerContribution := by
  intro C t E ht hE
  have h4 : 4 ≤ t := (le_max_left _ _).trans ht
  have hC : 2 * C ≤ t := (le_max_right _ _).trans ht
  have hsmall : 2 * (C * t) ≤ 2 ^ t := by
    have hmul := Nat.mul_le_mul_right t hC
    have hg := powerGrowth t h4
    nlinarith
  have hprod := Nat.mul_le_mul_right (2 ^ (E - t)) hsmall
  have hexp : 2 ^ t * 2 ^ (E - t) = 2 ^ E := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hE]
  unfold noise
  rw [← Nat.mul_assoc]
  exact hprod.trans_eq hexp

theorem halfPowerGap : Comparators.RayDominance.HalfPowerGap := by
  intro t E h4 hE
  have hpred : t - 1 < 2 ^ (t - 1) := Nat.lt_two_pow_self
  have hpow : 2 ^ (t - 1) ≤ 2 ^ (E - 1) :=
    Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_right hE 1)
  omega

theorem leadingSignAndGap : Comparators.RayDominance.LeadingSignAndGap := by
  intro C t E L remainder ht hE hlo hhi
  have h4 : 4 ≤ t := (le_max_left _ _).trans ht
  have hnoise : (2 : Int) * noise C t E ≤ (2 ^ E : Nat) := by
    exact_mod_cast lowerContribution C t E ht hE
  have hgap : (t : Int) ≤ (2 ^ (E - 1) : Nat) := by
    exact_mod_cast halfPowerGap t E h4 hE
  have hhalf : (2 ^ E : Nat) = 2 * 2 ^ (E - 1) := by
    calc
      2 ^ E = 2 ^ ((E - 1) + 1) := by congr 1; omega
      _ = 2 * 2 ^ (E - 1) := Nat.pow_succ'
  have hhalfZ : ((2 ^ E : Nat) : Int) = 2 * ((2 ^ (E - 1) : Nat) : Int) := by
    exact_mod_cast hhalf
  have hpowpos : (0 : Int) ≤ (2 ^ E : Nat) := Int.natCast_nonneg _
  constructor
  · intro hL
    have hL1 : (1 : Int) ≤ L := by omega
    have hmul := mul_le_mul_of_nonneg_right hL1 hpowpos
    unfold leadingValue
    nlinarith
  · intro hL
    have hL1 : L ≤ (-1 : Int) := by omega
    have hmul := mul_le_mul_of_nonneg_right hL1 hpowpos
    unfold leadingValue
    nlinarith

theorem rayDominance : Comparators.RayDominance.Target :=
  ⟨powerGrowth, lowerContribution, halfPowerGap, leadingSignAndGap⟩

end LogicLineages.ComputabilityKnowledge.RayDominanceProof
