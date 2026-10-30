module
public import LogicLineages.OrdinalComparison.ReserveStageCountTargets
public import LogicLineages.OrdinalComparison.ReserveStageInputProof
public import LogicLineages.OrdinalComparison.CompatiblePrefixFactsProof
public import LogicLineages.OrdinalComparison.ControlledCountProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

private theorem reserve_strict_gap {f : Nat → Nat} (hf : StrictMono f) (x X : Nat) (h : x ≤ X) :
    f x + X ≤ f X + x := by
  induction X, h using Nat.le_induction with
  | base => omega
  | succ X h ih =>
    have hs := hf (Nat.lt_succ_self X)
    change f X < f (X + 1) at hs
    change f x + (X + 1) ≤ f (X + 1) + x
    omega

private theorem reserve_iterate_growth (x d : Nat) : x + d ≤ (Phi^[d]) x := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Function.iterate_succ_apply']
    have hh := self_lt_Phi ((Phi^[d]) x)
    omega

theorem actualReserveIterationGap : Targets.ActualReserveIterationGap := by
  intro c X x d C hc hx hC
  have hgap := reserve_strict_gap (Phi_strictMono.iterate (d + 1)) x X hx
  have hcount := (Phi_strictMono.strictMono_iterate_of_lt_map (self_lt_Phi X)).monotone hC
  have hgrow := reserve_iterate_growth x d
  have htwice := reserveStageTwoMulLtPhi ((Phi^[d]) x)
  rw [Function.iterate_succ_apply'] at hgap
  omega

private theorem reserve_limitPart_tail (k : Ordinal) (hl : Order.IsSuccLimit k) (n : Nat) :
    actualLimitPart (k + (n : Ordinal)) = k := by
  obtain ⟨q, hq⟩ := Ordinal.isSuccPrelimit_iff_omega0_dvd.mp hl.isSuccPrelimit
  unfold actualLimitPart
  rw [hq, Ordinal.mul_add_div q Ordinal.omega0_ne_zero (n : Ordinal),
    Ordinal.div_eq_zero_of_lt (Ordinal.natCast_lt_omega0 n), add_zero]

theorem actualReserveStageCountLowerBound : Targets.ActualReserveStageCountLowerBound := by
  intro beta hb he k m n x hm rho hrho hbound hx hX
  dsimp only
  let pi := Ordinal.omega0 ^ beta
  let c := k * actualOrdinalNorm pi
  let R := pi * (m : Ordinal) + (n : Ordinal)
  let X := actualOrdinalNorm (pi * ((k + m : Nat) : Ordinal) + (n : Ordinal))
  let alpha := rho + ((x - actualOrdinalNorm rho : Nat) : Ordinal)
  let Q := actualMaximumPredecessor (pi * (m : Ordinal)) (Phi X - c)
  let g := compensatedPrefixControl c
  have hs := actualReserveStageDomain beta hb he k m n x hm rho hrho hbound hx hX
  have hq := actualReserveStageFirstResidual beta hb he k m n x hm rho hrho hbound hx hX
  dsimp only at hs hq
  have hpm := reserveStagePrincipalMultipleFacts beta he m
  have hR := actualFiniteTailClosureNorm (pi * (m : Ordinal)) hpm.1 n
  have htotal : c + actualOrdinalNorm R = X := by
    change c + actualOrdinalNorm (pi * (m : Ordinal) + (n : Ordinal)) = X
    rw [hR.2, hpm.2]
    have hformula := hs.2.1
    simpa only [c, pi, X, Nat.add_mul, Nat.add_assoc] using hformula.symm
  have hpl := Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (ne_of_gt hb)
  have hml : Order.IsSuccLimit (pi * (m : Ordinal)) :=
    Ordinal.isSuccLimit_mul_left hpl (by exact_mod_cast (show 0 < m by omega))
  have hstep : actualControlledStep g R = Q := by
    change actualMaximumPredecessor (actualLimitPart R) (Phi (c + actualOrdinalNorm R) - c) = Q
    rw [htotal]
    change actualMaximumPredecessor (actualLimitPart (pi * (m : Ordinal) + (n : Ordinal))) (Phi X - c) = Q
    rw [reserve_limitPart_tail _ hml n]
  have hQeps : Q < epsilonZero :=
    (actualMaximumPredecessor_correct _ hml.bot_lt hpm.1 (Phi X - c)).1.1.trans hpm.1
  have hcontrols := compensatedPrefixControlBounds c
  have hcompare : actualControlledCount Phi alpha ≤ actualControlledCount g Q :=
    actualControlledCountsJointMonotone Phi g (fun j => (hcontrols.2 j).1) hcontrols.1
      alpha Q hq.1 hQeps (by rw [hs.2.2.2.2.2.1]; exact hq.2.2)
  have hnon : Ordinal.omega0 ≤ R := (Ordinal.omega0_le_of_isSuccLimit hml).trans le_self_add
  have hc := (actualControlledCountRecursion g R hR.1).2 hnon
  rw [hstep] at hc
  exact (Nat.add_le_add_right hcompare 1).trans_eq hc.symm

end LogicLineages.OrdinalComparison
