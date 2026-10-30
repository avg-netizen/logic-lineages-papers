module
public import LogicLineages.OrdinalComparison.ReserveStageInputTargets
public import LogicLineages.OrdinalComparison.CompatiblePrefixNormProof
public import LogicLineages.OrdinalComparison.ActualCollapseBounds
public import LogicLineages.OrdinalComparison.ActualFiniteHead
public import LogicLineages.OrdinalComparison.Control

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem reserveStagePrincipalMultipleFacts (beta : Ordinal)
    (he : Ordinal.omega0 ^ beta < epsilonZero) (q : Nat) :
    Ordinal.omega0 ^ beta * (q : Ordinal) < epsilonZero ∧
    actualOrdinalNorm (Ordinal.omega0 ^ beta * (q : Ordinal)) =
      q * actualOrdinalNorm (Ordinal.omega0 ^ beta) := by
  induction q with
  | zero =>
    have hs := normalRepresentationSound ⟨ONote.zero, ONote.NF.zero⟩
    have hn := actualOrdinalNorm_notationCorrespondence ⟨ONote.zero, ONote.NF.zero⟩
    exact ⟨by simpa [ONote.repr] using hs,
      by simpa [ONote.repr, Vendor.R1.treeWeight] using hn⟩
  | succ q ih =>
    have hd : Ordinal.omega0 ^ beta ∣ Ordinal.omega0 ^ beta * (q : Ordinal) := dvd_mul_right _ _
    have hb : Ordinal.omega0 ^ beta < Ordinal.omega0 ^ (beta + 1) :=
      (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (lt_add_one beta)
    have hs := actualDivisiblePrefixNormAddition _ _ ih.1 he beta hd hb
    constructor
    · simpa only [Nat.cast_add, Nat.cast_one, mul_add, mul_one] using hs.1
    · simpa only [Nat.cast_add, Nat.cast_one, mul_add, mul_one, ih.2, Nat.succ_mul] using hs.2

theorem reserveStageTwoMulLtPhi (X : Nat) : 2 * X < Phi X := by
  have hp : X < 2 ^ X := Nat.lt_two_pow_self
  have hh : 2 * X < 2 ^ (X + 1) := by rw [Nat.pow_succ]; omega
  exact hh.trans_le ((Nat.pow_le_pow_right (by decide) (by omega : X + 1 ≤ X + 100)).trans
    (two_pow_shift_le_Phi X))

private theorem reserve_finite_tail_below (rho bound : Ordinal) (hb : Order.IsSuccLimit bound)
    (hr : rho < bound) (n : Nat) : rho + (n : Ordinal) < bound := by
  induction n with
  | zero => simpa using hr
  | succ n ih =>
    simpa only [Nat.cast_add, Nat.cast_one, Order.succ_eq_add_one, add_assoc] using hb.succ_lt ih

theorem actualReserveStageDomain : Targets.ActualReserveStageDomain := by
  intro beta hb he k m n x hm rho hrho hbound hx hX
  dsimp only
  let pi := Ordinal.omega0 ^ beta
  let w := actualOrdinalNorm pi
  let A := pi * ((k + m : Nat) : Ordinal) + (n : Ordinal)
  let X := actualOrdinalNorm A
  let c := k * w
  let alpha := rho + ((x - actualOrdinalNorm rho : Nat) : Ordinal)
  have hq := reserveStagePrincipalMultipleFacts beta he (k + m)
  have hpm := reserveStagePrincipalMultipleFacts beta he m
  have hA := actualFiniteTailClosureNorm (pi * ((k + m : Nat) : Ordinal)) hq.1 n
  have hformula : X = (k + m) * w + n := by
    change actualOrdinalNorm (pi * ((k + m : Nat) : Ordinal) + (n : Ordinal)) = _
    rw [hA.2, hq.2]
  have hc : c ≤ X := by
    have hmul := Nat.mul_le_mul_right w (Nat.le_add_right k m)
    change k * w ≤ X
    omega
  have hpl := Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (ne_of_gt hb)
  have hml : Order.IsSuccLimit (pi * (m : Ordinal)) :=
    Ordinal.isSuccLimit_mul_left hpl (by exact_mod_cast (show 0 < m by omega))
  have halpha : alpha < pi * (m : Ordinal) := reserve_finite_tail_below rho _ hml hbound _
  have hr : rho < epsilonZero := hbound.trans hpm.1
  have han := actualFiniteTailClosureNorm rho hr (x - actualOrdinalNorm rho)
  have hnorm : actualOrdinalNorm alpha = x := by rw [han.2, Nat.add_sub_of_le hx]
  have htwice := reserveStageTwoMulLtPhi X
  have hcx : c + x < Phi X := by
    change x ≤ X at hX
    omega
  exact ⟨hA.1, hformula, hc, halpha, halpha.trans hpm.1, hnorm, hcx⟩

theorem actualReserveStageFirstResidual : Targets.ActualReserveStageFirstResidual := by
  intro beta hb he k m n x hm rho hrho hbound hx hX
  dsimp only
  have hs := actualReserveStageDomain beta hb he k m n x hm rho hrho hbound hx hX
  dsimp only at hs
  have hpm := reserveStagePrincipalMultipleFacts beta he m
  have hpl := Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (ne_of_gt hb)
  have hml := Ordinal.isSuccLimit_mul_left hpl
    (show 0 < (m : Ordinal) by exact_mod_cast (show 0 < m by omega))
  have hmax := actualMaximumPredecessor_correct _ hml.bot_lt hpm.1
    (Phi (actualOrdinalNorm (Ordinal.omega0 ^ beta * ((k + m : Nat) : Ordinal) + (n : Ordinal))) -
      k * actualOrdinalNorm (Ordinal.omega0 ^ beta))
  have hnorm := actualLimitMaximumPredecessorSaturation _ hpm.1 hml
    (Phi (actualOrdinalNorm (Ordinal.omega0 ^ beta * ((k + m : Nat) : Ordinal) + (n : Ordinal))) -
      k * actualOrdinalNorm (Ordinal.omega0 ^ beta))
  refine ⟨hmax.2 ⟨hs.2.2.2.1, ?_⟩, hnorm, ?_⟩
  · rw [hs.2.2.2.2.2.1]
    have hh := hs.2.2.2.2.2.2
    omega
  · rw [hnorm]
    have hh := hs.2.2.2.2.2.2
    omega

end LogicLineages.OrdinalComparison
