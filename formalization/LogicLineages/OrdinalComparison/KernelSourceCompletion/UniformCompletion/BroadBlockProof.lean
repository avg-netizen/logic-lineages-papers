module
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.BroadBlockTargets
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.CalibrationProof
public import LogicLineages.OrdinalComparison.SuccessorKernelCutProof
public import LogicLineages.OrdinalComparison.ControlSegmentProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.Proof

private theorem power_norm (d : Nat) :
    actualOrdinalNorm (Ordinal.omega0 ^ (d : Ordinal)) = d+1 := by
  simpa only [Nat.cast_one,mul_one,Nat.mul_one] using (actualFiniteMonomialFacts d 1).2.1

private theorem next_power (n : Nat) :
    Ordinal.omega0 ^ ((n+1 : Nat) : Ordinal) * Ordinal.omega0 =
      Ordinal.omega0 ^ ((n+2 : Nat) : Ordinal) := by
  rw [← Ordinal.opow_add_one]
  congr 1

private theorem nat_norm (n : Nat) : actualOrdinalNorm (n : Ordinal) = n := by
  simpa only [Nat.cast_zero,mul_zero,zero_add,Nat.mul_zero,Nat.zero_add] using
    actualFiniteHeadNorm 0 n

theorem broadUnsignedBlockCut : Targets.BroadUnsignedBlockCut := by
  constructor
  · intro d c e j k R t hd hr
    have hd1 : 1 ≤ d := by omega
    have hbase : d ≤ 1000*d := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right d (by decide : 1 ≤ 1000)
    have hfactor : 1000*d ≤ 1000*d*d := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (1000*d) hd1
    have hD : d ≤ degreeConstant d := hbase.trans hfactor
    have hC : 1 ≤ degreeConstant d := by omega
    have hc : c ≤ degreeConstant d*c := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right c hC
    have he : e ≤ degreeConstant d*e := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right e hC
    have hsc : c+1 ≤ c+e+j.natAbs+k.natAbs+R+1 := by omega
    have hse : e+1 ≤ c+e+j.natAbs+k.natAbs+R+1 := by omega
    have hcb : degreeConstant d*c+degreeConstant d ≤ Phi t := by
      simpa only [Nat.mul_add,Nat.mul_one] using
        (Nat.mul_le_mul_left (degreeConstant d) hsc).trans hr.2
    have heb : degreeConstant d*e+degreeConstant d ≤ Phi t := by
      simpa only [Nat.mul_add,Nat.mul_one] using
        (Nat.mul_le_mul_left (degreeConstant d) hse).trans hr.2
    constructor <;> omega
  · intro n c t hb
    dsimp only
    let theta := Ordinal.omega0 ^ ((n+1 : Nat) : Ordinal)
    let parent := Ordinal.omega0 ^ ((n+2 : Nat) : Ordinal)
    let Q := firstSuffix (n+2) c t
    let r := firstSuffix (n+2) (c+n+2) t
    let h := compensatedPrefixControl c
    let g := compensatedPrefixControl (c+n+2)
    let C := actualControlledCount g r
    let L := actualControlledCount h Q
    let E := sourceCount (n+2) (c+n+2) t
    let K := sourceValue (n+2) (c+n+2) t
    have ho := firstBudgetCalibration (n+2) c t (by omega) (by omega)
    have hi := firstBudgetCalibration (n+2) (c+n+2) t (by omega) hb
    have hQeps : Q < epsilonZero := ho.2.1
    have hreps : r < epsilonZero := hi.2.1
    have hrparent : r < parent := hi.1
    have hEC : E = C+1 := hi.2.2.2.2.1
    have hOL : sourceCount (n+2) c t = L+1 := ho.2.2.2.2.1
    have hEpos : 1 ≤ E := by omega
    have hKge : Phi t ≤ K := by
      change (Phi^[1]) t ≤ (Phi^[E]) t
      exact iterate_index_mono (fun x => (self_lt_Phi x).le) t hEpos
    have hK : c+n+2 ≤ K := hb.trans hKge
    have hp : (0 : Ordinal) < ((n+1 : Nat) : Ordinal) := by
      exact_mod_cast (by omega : 0 < n+1)
    have htheta : theta < epsilonZero := finiteOmegaPowerBelowEpsilonZero (n+1)
    have hparent : theta*Ordinal.omega0 < epsilonZero := by
      rw [next_power n]
      exact finiteOmegaPowerBelowEpsilonZero (n+2)
    have hw : actualOrdinalNorm theta = n+2 := by simpa only [Nat.add_assoc] using power_norm (n+1)
    have hKnorm : c+actualOrdinalNorm theta ≤ K := by rw [hw]; exact hK
    have hshift : Q = theta+r := by
      have hm := actualSuccessorPrincipalMaximumShift ((n+1 : Nat) : Ordinal) hp hparent
        (Phi t-c) (by rw [hw]; omega)
      rw [next_power n,hw] at hm
      simpa only [Q,r,firstSuffix,theta,Nat.sub_sub,Nat.add_assoc] using hm
    have hmin : actualMinExponentAtLeast theta ((n+1 : Nat) : Ordinal) :=
      (actualMinExponentDivisibility theta htheta ((n+1 : Nat) : Ordinal)).mpr (dvd_refl theta)
    have hbound : r < Ordinal.omega0 ^ (((n+1 : Nat) : Ordinal)+1) := by
      rw [Ordinal.opow_add_one,next_power n]
      exact hrparent
    have hbudget : ∀ m : Nat, actualOrdinalNorm theta ≤ h (actualOrdinalNorm theta+m) := by
      intro m
      have hx := (compensatedPrefixControlBounds c).2 (actualOrdinalNorm theta+m)
      change actualOrdinalNorm theta ≤ compensatedPrefixControl c (actualOrdinalNorm theta+m)
      omega
    have hcontrols : prefixRemainderControl h (actualOrdinalNorm theta) = g := by
      dsimp only [h,g]
      rw [actualCompensatedControlComposition,hw]
      simp only [Nat.add_assoc]
    have hprefix := actualPrefixControlTrace h theta r htheta hreps ((n+1 : Nat) : Ordinal)
      hp hmin hbound hbudget
    have hdecomp := actualRetainedPrefixCountDecomposition h theta r htheta hreps
      ((n+1 : Nat) : Ordinal) hp hmin hbound hbudget
    dsimp only at hprefix hdecomp
    rw [hcontrols,← hshift] at hprefix hdecomp
    have hCL : C ≤ L := hdecomp.1
    have htrace : ∀ i : Nat, 1 ≤ i → i ≤ E →
        sourceState (n+2) c t i = theta+sourceState (n+2) (c+n+2) t i := by
      intro i hip hiE
      have hj : i-1 ≤ C := by omega
      have hjo : i-1 ≤ sourceCount (n+2) c t-1 := by omega
      have hji : i-1 ≤ E-1 := by omega
      have houter := (ho.2.2.2.2.2.2.1 (i-1) hjo).1
      have hinner := (hi.2.2.2.2.2.2.1 (i-1) hji).1
      have hadd : i-1+1 = i := by omega
      rw [hadd] at houter hinner
      rw [houter,hinner]
      exact hprefix.1 (i-1) hj
    have hinnerTrace := hi.2.2.2.2.2.2.1 C (by omega)
    have hinnerNorm : c+n+2+actualOrdinalNorm (actualControlledStateAfter g r C) = K := by
      have hn := hinnerTrace.2
      rw [hinnerTrace.1] at hn
      change c+n+2+actualOrdinalNorm (actualControlledStateAfter g r C) = (Phi^[C+1]) t at hn
      change c+n+2+actualOrdinalNorm (actualControlledStateAfter g r C) = (Phi^[E]) t
      rw [hEC]
      exact hn
    obtain ⟨m,hm⟩ := Ordinal.lt_omega0.mp (actualControlledTraceFirstFinite g r hreps).1
    have hfinite : actualControlledStateAfter g r C = (m : Ordinal) := hm
    rw [hfinite,nat_norm] at hinnerNorm
    have htail : K-c-actualOrdinalNorm theta = m := by rw [hw]; omega
    have hinnerExit : sourceState (n+2) (c+n+2) t E = (m : Ordinal) := by
      rw [hEC]
      exact hinnerTrace.1.trans hfinite
    have hcut : sourceState (n+2) c t E = actualSuffixKernelInitial theta c K := by
      change sourceState (n+2) c t E = theta+((K-c-actualOrdinalNorm theta : Nat) : Ordinal)
      rw [htrace E hEpos le_rfl,hinnerExit,htail]
    have hcutActual : theta+actualControlledStateAfter g r C = actualSuffixKernelInitial theta c K := by
      rw [hfinite]
      change theta+(m : Ordinal) = theta+((K-c-actualOrdinalNorm theta : Nat) : Ordinal)
      rw [htail]
    have hcounts := hdecomp.2.1
    rw [hcutActual] at hcounts
    change L = C+actualSuffixKernelCount theta c K at hcounts
    have htotal : sourceCount (n+2) c t = actualSuffixKernelCount theta c K+E := by omega
    have hchild := actualSuffixKernelTrace ((n+1 : Nat) : Ordinal) hp htheta c K hKnorm
    have hstrict : E < sourceCount (n+2) c t := by
      rw [htotal]
      have hpos : 0 < actualSuffixKernelCount theta c K := hchild.1
      omega
    refine ⟨hK,hKnorm,htrace,hstrict,hcut,htotal,?_⟩
    change (Phi^[sourceCount (n+2) c t]) t =
      (Phi^[actualSuffixKernelCount theta c K]) ((Phi^[E]) t)
    rw [htotal,Function.iterate_add_apply]

end LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.Proof
