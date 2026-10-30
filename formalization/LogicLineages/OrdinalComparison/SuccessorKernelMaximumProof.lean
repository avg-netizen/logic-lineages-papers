module
public import LogicLineages.OrdinalComparison.SuccessorKernelMaximumTargets
public import LogicLineages.OrdinalComparison.OptimizedMaximumGreedyProof
public import LogicLineages.OrdinalComparison.ActualFiniteHead

@[expose] public section
namespace LogicLineages.OrdinalComparison

private theorem successor_zero_norm : actualOrdinalNorm 0 = 0 := by
  simpa only [Nat.cast_zero, mul_zero, zero_add, Nat.mul_zero, Nat.add_zero] using actualFiniteHeadNorm 0 0

private theorem successor_weight (gamma : Ordinal) (he : gamma < epsilonZero) :
    actualOrdinalNorm (Ordinal.omega0 ^ gamma) = 1 + actualOrdinalNorm gamma := by
  have h := (actualCNFBlock gamma 0 he (Ordinal.opow_pos _ Ordinal.omega0_pos) ⟨1, by decide⟩).2.1
  simpa only [PNat.mk_coe, Nat.cast_one, mul_one, add_zero, Nat.one_mul,
    successor_zero_norm, Nat.add_zero] using h

private theorem successor_exponent_below (gamma : Ordinal)
    (he : Ordinal.omega0 ^ gamma * Ordinal.omega0 < epsilonZero) : gamma < epsilonZero :=
  (Ordinal.right_le_opow gamma Ordinal.one_lt_omega0).trans_lt
    ((Ordinal.le_mul_left _ Ordinal.omega0_pos).trans_lt he)

private theorem successor_block_norm (gamma : Ordinal) (he : gamma < epsilonZero)
    (q : Nat) (r : Ordinal) (hr : r < Ordinal.omega0 ^ gamma) :
    actualOrdinalNorm (Ordinal.omega0 ^ gamma * (q : Ordinal) + r) =
      q * actualOrdinalNorm (Ordinal.omega0 ^ gamma) + actualOrdinalNorm r := by
  by_cases hq : q = 0
  · simp [hq]
  · have h := (actualCNFBlock gamma r he hr ⟨q, Nat.pos_of_ne_zero hq⟩).2.1
    simpa only [PNat.mk_coe, successor_weight gamma he] using h

theorem actualSuccessorPrincipalWeight : Targets.ActualSuccessorPrincipalWeight := by
  intro gamma hg he
  rw [successor_weight gamma (successor_exponent_below gamma he)]
  omega

theorem actualSuccessorPrincipalMaximum : Targets.ActualSuccessorPrincipalMaximum := by
  intro gamma hg he b
  let theta := Ordinal.omega0 ^ gamma
  let w := actualOrdinalNorm theta
  let q := b / w
  let s := b % w
  have hgamma := successor_exponent_below gamma he
  have ht : theta < epsilonZero := (Ordinal.le_mul_left _ Ordinal.omega0_pos).trans_lt he
  have htheta : 0 < theta := Ordinal.opow_pos _ Ordinal.omega0_pos
  have hw : 0 < w := actualSuccessorPrincipalWeight gamma hg he
  have hM := actualMaximumPredecessor_correct theta htheta ht s
  have hdiv : q * w + s = b := by
    dsimp [q, s]
    simpa only [Nat.mul_comm] using Nat.div_add_mod b w
  change actualMaximumPredecessor (theta * Ordinal.omega0) b =
    theta * (q : Ordinal) + actualMaximumPredecessor theta s
  symm
  apply actualMaximumPredecessor_unique _ (mul_pos htheta Ordinal.omega0_pos) he b
  constructor
  · constructor
    · exact Ordinal.lt_mul_iff.mpr ⟨(q : Ordinal), Ordinal.natCast_lt_omega0 q,
        actualMaximumPredecessor theta s, hM.1.1, rfl⟩
    · rw [successor_block_norm gamma hgamma q _ hM.1.1]
      have hb := hM.1.2
      change q * w + actualOrdinalNorm (actualMaximumPredecessor theta s) ≤ b
      omega
  · intro x hx
    obtain ⟨k, hk, r, hr, hxr⟩ := Ordinal.lt_mul_iff.mp hx.1
    obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp hk
    rw [hn] at hxr
    have hnorm : n * w + actualOrdinalNorm r ≤ b := by
      have h := hx.2
      rw [hxr, successor_block_norm gamma hgamma n r hr] at h
      exact h
    have hnq : n ≤ q := (Nat.le_div_iff_mul_le hw).mpr (by omega)
    rw [hxr]
    rcases lt_or_eq_of_le hnq with hlt | rfl
    · have hcut : theta * (n : Ordinal) + r < theta * ((n + 1 : Nat) : Ordinal) := by
        simpa only [Nat.cast_add, Nat.cast_one, mul_add, mul_one] using
          (add_lt_add_right hr (theta * (n : Ordinal)))
      apply hcut.le.trans
      apply le_trans _ le_self_add
      apply mul_le_mul_left'
      exact_mod_cast Nat.succ_le_of_lt hlt
    · apply add_le_add_right
      exact hM.2 ⟨hr, by omega⟩

theorem actualSuccessorPrincipalMaximumShift : Targets.ActualSuccessorPrincipalMaximumShift := by
  intro gamma hg he b hb
  let theta := Ordinal.omega0 ^ gamma
  let w := actualOrdinalNorm theta
  have hw : 0 < w := actualSuccessorPrincipalWeight gamma hg he
  have hbw : b - w + w = b := Nat.sub_add_cancel hb
  have hq : b / w = (b - w) / w + 1 := by
    conv_lhs => rw [← hbw]
    exact Nat.add_div_right _ hw
  have hs : b % w = (b - w) % w := by
    conv_lhs => rw [← hbw]
    exact Nat.add_mod_right _ _
  rw [actualSuccessorPrincipalMaximum gamma hg he b,
    actualSuccessorPrincipalMaximum gamma hg he (b - w)]
  change theta * ((b / w : Nat) : Ordinal) + actualMaximumPredecessor theta (b % w) =
    theta + (theta * (((b - w) / w : Nat) : Ordinal) + actualMaximumPredecessor theta ((b - w) % w))
  rw [hq, hs]
  have hc : theta * (((b - w) / w : Nat) : Ordinal) + theta =
      theta + theta * (((b - w) / w : Nat) : Ordinal) := by
    calc
      _ = theta * ((((b - w) / w + 1 : Nat)) : Ordinal) := by simp [Nat.cast_add, mul_add]
      _ = theta * (((1 + (b - w) / w : Nat)) : Ordinal) := by rw [Nat.add_comm]
      _ = _ := by simp [Nat.cast_add, mul_add]
  simpa only [Nat.cast_add, Nat.cast_one, mul_add, mul_one, hc, add_assoc]

end LogicLineages.OrdinalComparison
