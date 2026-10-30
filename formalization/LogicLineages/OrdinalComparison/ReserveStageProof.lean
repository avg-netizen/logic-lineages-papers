module
public import LogicLineages.OrdinalComparison.ReserveStageTargets
public import LogicLineages.OrdinalComparison.ReserveStageCountProof
public import LogicLineages.OrdinalComparison.PrefixTraceGeneralProof
public import LogicLineages.OrdinalComparison.ControlScheduleProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem reserveCompensatedIteration (c n i : Nat) :
    c + ((compensatedPrefixControl c)^[i]) n = (Phi^[i]) (c + n) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have hb := self_lt_Phi (c + ((compensatedPrefixControl c)^[i]) n)
    change c + (Phi (c + ((compensatedPrefixControl c)^[i]) n) - c) = _
    rw [Nat.add_sub_of_le (by omega), ih]

private theorem stage_nat_norm (n : Nat) : actualOrdinalNorm (n : Ordinal) = n := by
  simpa only [Nat.cast_zero, mul_zero, zero_add, Nat.mul_zero, Nat.zero_add] using actualFiniteHeadNorm 0 n

theorem fullActualOneStageReserve : Targets.FullActualOneStageReserve := by
  intro beta hb he k m n x hm rho hrho hbound hx hX
  dsimp only
  let pi := Ordinal.omega0 ^ beta
  let c := k * actualOrdinalNorm pi
  let R := pi * (m : Ordinal) + (n : Ordinal)
  let alpha := rho + ((x - actualOrdinalNorm rho : Nat) : Ordinal)
  let C := actualControlledCount (compensatedPrefixControl c) R
  let D := actualControlledCount Phi alpha
  let retained := pi * (k : Ordinal)
  let A := pi * ((k + m : Nat) : Ordinal) + (n : Ordinal)
  let X := actualOrdinalNorm A
  have hs := actualReserveStageDomain beta hb he k m n x hm rho hrho hbound hx hX
  have hC := actualReserveStageCountLowerBound beta hb he k m n x hm rho hrho hbound hx hX
  change D + 1 ≤ C at hC
  have hk := reserveStagePrincipalMultipleFacts beta he k
  have hpm := reserveStagePrincipalMultipleFacts beta he m
  have hR := actualFiniteTailClosureNorm (pi * (m : Ordinal)) hpm.1 n
  have hmin : actualMinExponentAtLeast retained beta :=
    (actualMinExponentDivisibility retained hk.1 beta).mpr (dvd_mul_right _ _)
  have hpl := Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 (ne_of_gt hb)
  have hn : (n : Ordinal) < pi :=
    (Ordinal.natCast_lt_omega0 n).trans_le (Ordinal.omega0_le_of_isSuccLimit hpl)
  have hRb : R < Ordinal.omega0 ^ (beta + 1) :=
    Ordinal.opow_mul_add_lt_opow (Ordinal.natCast_lt_omega0 m) hn (lt_add_one beta)
  have hbudget : ∀ j : Nat, actualOrdinalNorm retained ≤ Phi (actualOrdinalNorm retained + j) := by
    intro j
    have hh := self_lt_Phi (actualOrdinalNorm retained + j)
    omega
  have hp := actualPrefixControlTrace Phi retained R hk.1 hR.1 beta hb hmin hRb hbudget
  dsimp only at hp
  rw [hk.2] at hp
  have hcontrol : prefixRemainderControl Phi c = compensatedPrefixControl c := rfl
  rw [hcontrol] at hp
  have hA : A = retained + R := by
    simp only [A, retained, R, Nat.cast_add, mul_add, add_assoc]
  have htotal : c + actualOrdinalNorm R = X := by
    change c + actualOrdinalNorm (pi * (m : Ordinal) + (n : Ordinal)) = X
    rw [hR.2, hpm.2]
    have hformula := hs.2.1
    simpa only [c, pi, X, A, Nat.add_mul, Nat.add_assoc] using hformula.symm
  have htrace : ∀ i : Nat, i ≤ C → actualControlledStateAfter Phi A i =
      retained + actualControlledStateAfter (compensatedPrefixControl c) R i := by
    intro i hi
    rw [hA]
    exact hp.1 i hi
  have hnon : ∀ i : Nat, i < C → retained + Ordinal.omega0 ≤ actualControlledStateAfter Phi A i := by
    intro i hi
    rw [hA]
    exact hp.2.2 i hi
  obtain ⟨n', hn'⟩ := Ordinal.lt_omega0.mp hp.2.1
  have hnorm := actualControlledNormIteration (compensatedPrefixControl c) R hR.1 C le_rfl
  have hiter := reserveCompensatedIteration c (actualOrdinalNorm R) C
  rw [← hnorm, hn', stage_nat_norm, htotal] at hiter
  have hcX : c ≤ X := hs.2.2.1
  have hxX : x ≤ X := hX
  have hgap := actualReserveIterationGap c X x D C hcX hxX hC
  refine ⟨(Nat.zero_lt_succ D).trans_le hC, htrace, hnon, n', ?_, ?_⟩
  · rw [htrace C le_rfl, hn']
  · change (Phi^[D]) x + D < n'
    have htail : (Phi^[C]) X - c = n' := by
      rw [← hiter, Nat.add_sub_cancel_left]
    exact hgap.trans_eq htail

end LogicLineages.OrdinalComparison
