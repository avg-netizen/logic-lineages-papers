module
public import LogicLineages.StandardControlCurrent.NumericalKernelProcessProof
public import LogicLineages.OrdinalComparison.SmallKernelsProof
public import LogicLineages.OrdinalComparison.FiniteKernelRecursionProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.NumericalKernelProof
open OrdinalComparison NumericalKernel

theorem omega_count (c t : Nat) : count 1 c t = 1 := by
  have hn : ((Phi t-c : Nat) : Ordinal) < epsilonZero :=
    (Ordinal.natCast_lt_omega0 _).trans (by simpa using finiteOmegaPowerBelowEpsilonZero 1)
  have h := (actualControlledCountRecursion (compensatedPrefixControl c) _ hn).1
    (Ordinal.natCast_lt_omega0 (Phi t-c))
  simpa only [count,first,Nat.cast_one,Ordinal.opow_one,actualOmegaMaximum,h,Nat.add_zero]

theorem square_max_all (b : Nat) : actualMaximumPredecessor (Ordinal.omega0 ^ (2 : Ordinal)) b =
    Ordinal.omega0 * ((b/2 : Nat) : Ordinal)+((b%2 : Nat) : Ordinal) := by
  by_cases hb : 2 ≤ b
  · exact actualOmegaSquaredMaximum b hb
  have he : (2 : Ordinal) < epsilonZero := (Ordinal.natCast_lt_omega0 2).trans
    (by simpa using finiteOmegaPowerBelowEpsilonZero 1)
  have hp : (0 : Ordinal) < Ordinal.omega0 ^ (2 : Ordinal) := Ordinal.opow_pos _ Ordinal.omega0_pos
  have hpe := finiteOmegaPowerBelowEpsilonZero 2
  have hcases : b=0 ∨ b=1 := by omega
  rcases hcases with rfl | rfl
  · simpa using actualOptimizedMaximumBaseCases.1 _ hp hpe
  · have hr := actualLowerPowerGreedyRecurrence (2 : Ordinal) (by norm_num) he 1 (by omega)
    dsimp only at hr
    rw [show 1-1=0 by omega,actualOptimizedMaximumBaseCases.1 _ (by norm_num) he] at hr
    have hz : actualOrdinalNorm 0=0 := by
      simpa using (actualFiniteHeadNorm 0 0)
    simp only [hz,Nat.add_zero,Nat.div_one,Nat.mod_one,Ordinal.opow_zero,Nat.cast_one,
      one_mul,actualOptimizedMaximumBaseCases.2.2 _ (by simpa using he),add_zero] at hr
    simpa [actualLowerPowerMaximum] using hr

theorem square_count (c t : Nat) (hc : c ≤ Phi t) :
    count 2 c t = Phi t/2-(c+1)/2+1 := by
  have hg : ∀ n : Nat, n ≤ compensatedPrefixControl c n := by
    intro n
    have := self_lt_Phi (c+n)
    unfold compensatedPrefixControl
    omega
  have h := actualExpansiveControlLinearCount _ hg ((Phi t-c)/2) ((Phi t-c)%2)
  have heven : Phi t%2=0 := Nat.even_iff.mp (actualPhiEven t)
  unfold count first
  rw [show ((2 : Nat) : Ordinal) = 2 by rfl,square_max_all,h]
  omega

theorem depth_agreement (d c t : Nat) (hd : 1 ≤ d) (ht : c+d+1 ≤ t) (j : Int) :
    depth d c j t = signedKernelDepth d c j t := by
  unfold depth signedKernelDepth
  rw [(padded d c t hd ht).1]

theorem bases : NumericalKernelTargets.Bases := by
  refine ⟨?_,square_count,?_,?_⟩
  · intro c t hc
    exact ⟨omega_count c t,by simp only [value,omega_count,Function.iterate_one]⟩
  · intro c t hc j
    have heven : Phi t%2=0 := Nat.even_iff.mp (actualPhiEven t)
    have hle : (c+1)/2 ≤ Phi t/2 := by omega
    have hd : depth 2 c j t = ((Phi t/2 : Nat) : Int)+(j-(((c+1)/2 : Nat) : Int))+1 := by
      unfold depth
      rw [square_count c t hc]
      omega
    exact ⟨hd,by simp only [signed,hd,rawQuadraticShift]⟩
  · intro c j t ht
    have hdom : c+2*2+1 ≤ t := (Nat.le_max_left _ _).trans ht
    have hlarge : c+2*j.natAbs+3 ≤ t := (Nat.le_max_right _ _).trans ht
    have h := SignedKernelDomainProof.finiteDegreeCounterLowerBound.2 2 c j.natAbs t (by omega)
      (max_le (by omega) hlarge)
    rw [depth_agreement 2 c t (by omega) (by omega) j]
    have hj : -(j.natAbs : Int) ≤ j := by cases j <;> simp <;> omega
    unfold signedKernelDepth
    omega
end LogicLineages.StandardControlCurrent.NumericalKernelProof
