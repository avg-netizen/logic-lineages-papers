module
public import LogicLineages.OrdinalComparison.SignedPhiSeparationEvaluationProof
public import LogicLineages.OrdinalComparison.ControlHierarchyGrowthProof
public import LogicLineages.OrdinalComparison.Control
public import Mathlib.Tactic.Linarith

@[expose] public section
namespace LogicLineages.OrdinalComparison.SignedPhiSeparation.Proof
open SignedShiftCollection

set_option maxHeartbeats 200000

/-- The triangle inequality pays only for the coefficients in the given row.
It is applied below to the surviving blocks strictly below the greatest key. -/
private theorem weighted_abs_bound (row : CommonHeadLargeRow.Row)
    (f : Nat → Nat) (U : Nat) (hv : ∀ a ∈ row, f a.2 ≤ U) :
    ((row.map (fun a => a.1 * (f a.2 : Int))).sum).natAbs ≤
      (row.map (fun a => a.1.natAbs)).sum * U := by
  induction row with
  | nil => simp
  | cons a rest ih =>
    have ha := hv a List.mem_cons_self
    have hr := ih (fun b hb => hv b (List.mem_cons_of_mem a hb))
    have hadd := Int.natAbs_add_le (a.1 * (f a.2 : Int))
      ((rest.map (fun b => b.1 * (f b.2 : Int))).sum)
    simp only [Int.natAbs_mul, Int.natAbs_natCast] at hadd
    simp only [List.map_cons, List.sum_cons]
    calc
      (a.1 * (f a.2 : Int) +
          (rest.map (fun b => b.1 * (f b.2 : Int))).sum).natAbs ≤
          a.1.natAbs * f a.2 +
            ((rest.map (fun b => b.1 * (f b.2 : Int))).sum).natAbs := hadd
      _ ≤ a.1.natAbs * U + (rest.map (fun b => b.1.natAbs)).sum * U :=
        Nat.add_le_add (Nat.mul_le_mul_left a.1.natAbs ha) hr
      _ = (a.1.natAbs + (rest.map (fun b => b.1.natAbs)).sum) * U :=
        (Nat.add_mul _ _ _).symm

private theorem separation_at (row : Row) (hne : collected row ≠ []) (x : Nat) :
    (0 < leadingCoefficient row →
      (Phi x : Int) < value row (shiftedInput row x)) ∧
    (leadingCoefficient row < 0 →
      value row (shiftedInput row x) < -(Phi x : Int)) := by
  let z : Nat := ((x : Int) + (delta row : Int) + greatestShift row - 1).toNat
  let R : Int := CommonHeadCollectedRow.weighted
    (fun k => (Phi (rebasedInput row x + k) : Int)) (lowerRow row)
  have hdomain := exactSourceShiftAndArguments row
  have hD : domainOffset row ≤ delta row := hdomain.2.1
  have hdelta := hdomain.2.2.2.1 hne
  have hsource : (lowerMass row : Int) + 1 - greatestShift row ≤
      (delta row : Int) := by
    rw [hdelta]
    exact le_max_right _ _
  have hznonneg : 0 ≤ (x : Int) + (delta row : Int) + greatestShift row - 1 := by
    omega
  have hzcast : (z : Int) =
      (x : Int) + (delta row : Int) + greatestShift row - 1 :=
    Int.toNat_of_nonneg hznonneg
  have hlarge : x + lowerMass row ≤ z := by omega
  have hlead : argument (shiftedInput row x) (greatestShift row) = z + 1 := by
    unfold argument shiftedInput
    omega
  have hrebased : (rebasedInput row x : Int) =
      (x : Int) + (delta row : Int) - (domainOffset row : Int) := by
    unfold rebasedInput
    omega
  have hgreatest : greatestShift row =
      (greatestKey row : Int) - (domainOffset row : Int) := rfl
  have hlower : ∀ a ∈ lowerRow row, rebasedInput row x + a.2 ≤ z := by
    intro a ha
    have hk : a.2 < greatestKey row := by
      have hm := (List.mem_filter.mp ha).2
      exact of_decide_eq_true hm
    omega
  have hRnat : R.natAbs ≤ lowerMass row * Phi z := by
    exact weighted_abs_bound (lowerRow row)
      (fun k => Phi (rebasedInput row x + k)) (Phi z)
      (fun a ha => Phi_strictMono.monotone (hlower a ha))
  have hR : |R| ≤ (lowerMass row : Int) * (Phi z : Int) := by
    have hc : (R.natAbs : Int) ≤ ((lowerMass row * Phi z : Nat) : Int) := by
      exact_mod_cast hRnat
    simpa only [Int.natCast_natAbs, Nat.cast_mul] using hc
  have hgrowth : ((lowerMass row : Int) + 2) * (Phi z : Int) ≤
      (Phi (z + 1) : Int) := by
    have hg := fullFastControlHierarchyGrowth.2.2 (lowerMass row) z (by omega)
    exact_mod_cast hg
  have hpositive : 0 < (Phi z : Int) := by
    have hp : 0 < Phi z := (Nat.zero_le z).trans_lt (self_lt_Phi z)
    exact_mod_cast hp
  have hmonotone : (Phi x : Int) ≤ (Phi z : Int) := by
    have hm := Phi_strictMono.monotone (show x ≤ z by omega)
    exact_mod_cast hm
  have hstrict : (Phi x : Int) < 2 * (Phi z : Int) := by omega
  have heval : value row (shiftedInput row x) =
      leadingCoefficient row * (Phi (z + 1) : Int) + R := by
    simpa only [hlead] using (exactEvaluationAndCancellation row).2.2 hne x
  have hphinonneg : (0 : Int) ≤ (Phi (z + 1) : Int) := Int.natCast_nonneg _
  constructor
  · intro hc
    have hc1 : (1 : Int) ≤ leadingCoefficient row := by omega
    have hleading : (Phi (z + 1) : Int) ≤
        leadingCoefficient row * (Phi (z + 1) : Int) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hc1 hphinonneg
    have hRlower := (abs_le.mp hR).1
    calc
      (Phi x : Int) < 2 * (Phi z : Int) := hstrict
      _ ≤ leadingCoefficient row * (Phi (z + 1) : Int) + R := by
        nlinarith only [hRlower, hleading, hgrowth]
      _ = value row (shiftedInput row x) := heval.symm
  · intro hc
    have hc1 : leadingCoefficient row ≤ (-1 : Int) := by omega
    have hleading : leadingCoefficient row * (Phi (z + 1) : Int) ≤
        -(Phi (z + 1) : Int) := by
      simpa only [neg_one_mul] using mul_le_mul_of_nonneg_right hc1 hphinonneg
    have hRupper := (abs_le.mp hR).2
    calc
      value row (shiftedInput row x) =
          leadingCoefficient row * (Phi (z + 1) : Int) + R := heval
      _ ≤ -(2 * (Phi z : Int)) := by
        nlinarith only [hRupper, hleading, hgrowth]
      _ < -(Phi x : Int) := by omega

/-- The exact source shift separates the actual signed sum from both Phi and
-Phi. The leading coefficient and all lower blocks are the actual collection. -/
theorem actualSignedPhiSeparation : Targets.ActualSignedPhiSeparation := by
  intro row hne
  constructor
  · intro hc x
    exact (separation_at row hne x).1 hc
  · intro hc x
    exact (separation_at row hne x).2 hc

end LogicLineages.OrdinalComparison.SignedPhiSeparation.Proof
