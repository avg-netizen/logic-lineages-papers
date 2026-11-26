module
public import LogicLineages.StandardControlCurrent.UniformSeparationTargets
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.QuantitativeStatementChecks
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.CalibrationStatementChecks
@[expose] public section
namespace LogicLineages.StandardControlCurrent.UniformSeparationProof
open OrdinalComparison NumericalKernel
open OrdinalComparison.KernelSourceCompletion
open OrdinalComparison.KernelSourceCompletion.UniformCompletion

theorem calibration : UniformSeparationTargets.ScheduledCalibration := by
  intro d c t hd hc
  have h := StatementChecks.first_budget_calibration d c t hd hc
  dsimp only at h
  have he : sourceCount d c t = count d c t := by
    have hh := h.2.2.2.2.1
    change sourceCount d c t = actualControlledCount (compensatedPrefixControl c) (first d c t)+1 at hh
    unfold count
    omega
  refine ⟨he,?_,?_⟩
  · simp only [sourceValue,value,he]
  · intro j
    have hj : sourceSignedDepth d c j t = depth d c j t := by
      simp only [sourceSignedDepth,depth,he]
    exact ⟨hj,by simp only [sourceSignedValue,signed,hj]⟩

theorem region_masses (d c e : Nat) (j k : Int) (R t : Nat) (hd : 3 ≤ d)
    (hr : region d c e j k R t) : c ≤ Phi t ∧ e ≤ Phi t := by
  have hpos : 1 ≤ degreeConstant d := by unfold degreeConstant; nlinarith
  have hs : c+e+j.natAbs+k.natAbs+R+1 ≤ Phi t :=
    (Nat.le_mul_of_pos_left _ hpos).trans hr.2
  omega

theorem full : UniformSeparationTargets.Full := by
  have old := QuantitativeStatementChecks.full_uniform_source
  refine ⟨calibration,?_,?_,?_,?_,old.2.2.2.2⟩
  · intro d c e j k R t hd hr
    have hm := region_masses d c e j k R t hd hr
    have hg := (Phi_strictMono (Nat.lt_succ_self t)).le
    have cc := (calibration d c t (by omega) hm.1).2.2 j
    have ec := (calibration d e t (by omega) hm.2).2.2 k
    have cn := (calibration d c (t+1) (by omega) (hm.1.trans hg)).2.2 j
    have en := (calibration d e (t+1) (by omega) (hm.2.trans hg)).2.2 k
    simpa only [cc.1,cc.2,ec.1,ec.2,cn.1,cn.2,en.1,en.2] using old.1 d c e j k R t hd hr
  · intro d c e j k R t hd hr
    have hm := region_masses d c e j k R t hd hr
    have hg := (Phi_strictMono (Nat.lt_succ_self t)).le
    have cc := (calibration d c t (by omega) hm.1).2.2 j
    have ec := (calibration d e t (by omega) hm.2).2.2 k
    have cn := (calibration d c (t+1) (by omega) (hm.1.trans hg)).2.2 j
    simpa only [cc.2,ec.2,cn.2] using old.2.1 d c e j k R t hd hr
  · intro d c t hd hc j k hj hk
    have cj := (calibration d c t (by omega) hc).2.2 j
    have ck := (calibration d c t (by omega) hc).2.2 k
    rw [← cj.1] at hj
    rw [← ck.1] at hk
    simpa only [cj.2,ck.2] using old.2.2.1 d c t hd hc j k hj hk
  · intro d c e j k hd t u ht hu
    have h := old.2.2.2.1 d c e j k hd t u ht hu
    have cj := (calibration d c t (by omega) h.1).2.2 j
    have ek := (calibration d e u (by omega) h.2.1).2.2 k
    simpa only [cj.1,cj.2,ek.1,ek.2] using h
end LogicLineages.StandardControlCurrent.UniformSeparationProof
