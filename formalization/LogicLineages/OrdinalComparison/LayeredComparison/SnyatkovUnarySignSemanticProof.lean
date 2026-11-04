module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovUnarySignTargets
public import LogicLineages.OrdinalComparison.SignedPhiSeparationGrowthProof
public import LogicLineages.OrdinalComparison.ControlHierarchyGrowthProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovUnarySign.Proof
open SignedShiftCollection

private theorem phi_quadratic (n : Nat) : n * (n + 1) ≤ Phi n := by
  cases n with
  | zero => exact Nat.zero_le _
  | succ n =>
    have hl : n + 1 ≤ Phi n := self_lt_Phi n
    calc
      (n + 1) * (n + 1 + 1) = (n + 2) * (n + 1) := by
        rw [Nat.mul_comm]
      _ ≤ (n + 2) * Phi n := Nat.mul_le_mul_left _ hl
      _ ≤ Phi (n + 1) := fullFastControlHierarchyGrowth.2.2 n n le_rfl

private theorem threshold_domain (E : Expression) : domainBound E ≤ threshold E := by
  unfold threshold
  split
  · exact le_max_left _ _
  · have h := SignedPhiSeparation.Proof.domainOffset_le_delta E.1
    change domainOffset E.1 ≤ _
    omega

private theorem remainder_bound (E : Expression) (n : Nat)
    (hn : SignedPhiSeparation.delta E.1 +
      (E.2.1.natAbs + E.2.1.natAbs * SignedPhiSeparation.delta E.1 + E.2.2.natAbs + 1) ≤ n) :
    E.2.1.natAbs * n + E.2.2.natAbs < Phi (n - SignedPhiSeparation.delta E.1) := by
  let x := n - SignedPhiSeparation.delta E.1
  have hd : SignedPhiSeparation.delta E.1 ≤ n := by omega
  have heq : x + SignedPhiSeparation.delta E.1 = n := Nat.sub_add_cancel hd
  have hA : E.2.1.natAbs ≤ x := by dsimp [x]; omega
  have hB : E.2.1.natAbs * SignedPhiSeparation.delta E.1 + E.2.2.natAbs < x := by
    dsimp [x]; omega
  calc
    E.2.1.natAbs * n + E.2.2.natAbs =
        E.2.1.natAbs * x +
          (E.2.1.natAbs * SignedPhiSeparation.delta E.1 + E.2.2.natAbs) := by
      rw [← heq, Nat.mul_add, Nat.add_assoc]
    _ < x * x + x := Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul_right x hA) hB
    _ = x * (x + 1) := by rw [Nat.mul_add, Nat.mul_one]
    _ ≤ Phi x := phi_quadratic x

private theorem linear_bounds (c d : Int) (n : Nat) :
    -((c.natAbs * n + d.natAbs : Nat) : Int) ≤ c * (n : Int) + d ∧
    c * (n : Int) + d ≤ ((c.natAbs * n + d.natAbs : Nat) : Int) := by
  have hc := Int.le_natAbs (a := c)
  have hd := Int.le_natAbs (a := d)
  have hc' := Int.le_natAbs (a := -c)
  have hd' := Int.le_natAbs (a := -d)
  simp only [Int.natAbs_neg] at hc' hd'
  have hu := mul_le_mul_of_nonneg_right hc (show (0 : Int) ≤ n by omega)
  have hl := mul_le_mul_of_nonneg_right hc' (show (0 : Int) ≤ n by omega)
  simp only [neg_mul] at hl
  simp only [Nat.cast_add, Nat.cast_mul]
  omega

private theorem cancelled_value (E : Expression) (h : collected E.1 = [])
    (n : Nat) (hn : domainBound E ≤ n) :
    value E n = E.2.1 * (n : Int) + E.2.2 := by
  have hz := SignedPhiSeparation.Proof.evaluation_collected E.1 (n - domainBound E)
  have heq : SignedPhiSeparation.shiftedInput E.1 (n - domainBound E) = n := by
    unfold SignedPhiSeparation.shiftedInput
    rw [SignedPhiSeparation.Proof.delta_of_cancelled E.1 h]
    exact Nat.sub_add_cancel hn
  rw [heq, h] at hz
  simp only [CommonHeadCollectedRow.weighted, List.map_nil, List.sum_nil] at hz
  simp only [value, hz, zero_add]

private theorem cancelled_sign (E : Expression) (h : collected E.1 = [])
    (n : Nat) (hn : threshold E ≤ n) : Int.sign (value E n) = tailSign E := by
  have hD := (threshold_domain E).trans hn
  have hbig : E.2.2.natAbs < n := by
    simp only [threshold, h, ↓reduceIte] at hn
    omega
  rw [cancelled_value E h n hD]
  unfold tailSign
  rw [if_pos h]
  by_cases hc : E.2.1 = 0
  · simp only [hc, zero_mul, zero_add, ↓reduceIte]
  · rw [if_neg hc]
    have hbounds := linear_bounds E.2.1 E.2.2 n
    by_cases hp : 0 < E.2.1
    · have hm := mul_le_mul_of_nonneg_right (show (1 : Int) ≤ E.2.1 by omega)
        (show (0 : Int) ≤ n by omega)
      have hd := Int.le_natAbs (a := -E.2.2)
      simp only [one_mul, Int.natAbs_neg] at hm hd
      rw [Int.sign_eq_one_of_pos hp, Int.sign_eq_one_of_pos (by omega)]
    · have hm := mul_le_mul_of_nonneg_right (show E.2.1 ≤ (-1 : Int) by omega)
        (show (0 : Int) ≤ n by omega)
      have hd := Int.le_natAbs (a := E.2.2)
      simp only [neg_one_mul] at hm
      rw [Int.sign_eq_neg_one_of_neg (by omega : E.2.1 < 0),
        Int.sign_eq_neg_one_of_neg (by omega)]

private theorem surviving_sign (E : Expression) (h : collected E.1 ≠ [])
    (n : Nat) (hn : threshold E ≤ n) : Int.sign (value E n) = tailSign E := by
  have hthreshold := hn
  simp only [threshold, h, ↓reduceIte] at hthreshold
  have hr := remainder_bound E n hthreshold
  have hmass : (((E.2.1.natAbs * n + E.2.2.natAbs : Nat) : Int)) <
      (Phi (n - SignedPhiSeparation.delta E.1) : Int) := Int.ofNat_lt.mpr hr
  have hb := linear_bounds E.2.1 E.2.2 n
  have hd : SignedPhiSeparation.delta E.1 ≤ n := by omega
  have heq : SignedPhiSeparation.shiftedInput E.1 (n - SignedPhiSeparation.delta E.1) = n :=
    Nat.sub_add_cancel hd
  have hne := (SignedShiftCollection.Proof.actualGreatestSurvivingShift E.1 h).2.1
  unfold tailSign
  rw [if_neg h]
  by_cases hp : 0 < leadingCoefficient E.1
  · have hs := (SignedPhiSeparation.Proof.actualSignedPhiSeparation E.1 h).1 hp
      (n - SignedPhiSeparation.delta E.1)
    rw [heq] at hs
    rw [Int.sign_eq_one_of_pos hp, Int.sign_eq_one_of_pos]
    unfold value
    omega
  · have hneg : leadingCoefficient E.1 < 0 := by omega
    have hs := (SignedPhiSeparation.Proof.actualSignedPhiSeparation E.1 h).2 hneg
      (n - SignedPhiSeparation.delta E.1)
    rw [heq] at hs
    rw [Int.sign_eq_neg_one_of_neg hneg, Int.sign_eq_neg_one_of_neg]
    unfold value
    omega

theorem originalDomainAndTailSign : Targets.OriginalDomainAndTailSign := by
  intro E
  refine ⟨threshold_domain E, ?_⟩
  intro n hn
  have hd := (threshold_domain E).trans hn
  refine ⟨(SignedShiftCollection.Proof.domainOffset_le_iff E.1 n).mp hd, ?_⟩
  by_cases h : collected E.1 = []
  · exact cancelled_sign E h n hn
  · exact surviving_sign E h n hn

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovUnarySign.Proof
