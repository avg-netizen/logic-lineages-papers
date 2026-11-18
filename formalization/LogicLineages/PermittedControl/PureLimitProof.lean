module
public import LogicLineages.PermittedControl.PureLimitTargets
public import LogicLineages.PermittedControl.PureSuccessorSeparationProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem pure_limit_calibration (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (mu E zeta A : Ordinal.{0}) (R t : Nat)
    (hmu : mu < epsilonZero) (hE : E < epsilonZero) (hz : zeta < epsilonZero) (hA : A < epsilonZero)
    (hEl : Order.IsSuccLimit E) (hz2 : 2 ≤ zeta) (hzE : zeta < E)
    (hmuR : actualOrdinalNorm mu ≤ R) (hzR : actualOrdinalNorm zeta ≤ R)
    (ht : thickBlockTail R B ≤ t) (hp : actualLimitPart A=mu+Ordinal.omega0^E)
    (hn : actualOrdinalNorm A=t)
    (hc : ∀ e : Ordinal.{0}, zeta ≤ e → e < E → relativeProfile mu e=relativeProfile mu zeta) :
    descentWith f A-mu=actualMaximumPredecessor (Ordinal.omega0^E) (f t-relativeProfile mu zeta) ∧
    actualOrdinalNorm (descentWith f A)=f t ∧
    Ordinal.omega0^zeta ≤ actualLimitPart (descentWith f A-mu) ∧
    0 < f t-relativeProfile mu zeta := by
  have hzpos : 0 < zeta := (by norm_num : (0 : Ordinal) < 2).trans_le hz2
  have hP := phase_power_below zeta hz
  have hY := phase_power_below E hE
  have hPpos := Ordinal.opow_pos zeta Ordinal.omega0_pos
  have hPY := (Ordinal.isNormal_opow Ordinal.one_lt_omega0).strictMono hzE
  have hPl := Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 hzpos.ne'
  have hYl := Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 hEl.bot_lt.ne'
  have hlarge := sensitive_tail_double R B t ht
  have hu := (G_large t).trans ((selected_threshold_admissible f B hf).2 t)
  have hcR := (relativePrefixNorm mu zeta hmu).2.2.trans hmuR
  have hPN : actualOrdinalNorm (Ordinal.omega0^zeta)=1+actualOrdinalNorm zeta := by
    simpa only [Nat.cast_one,mul_one,one_mul] using thick_monomial_norm zeta hz 1
  have hrel := relativeNorm mu (Ordinal.omega0^zeta) hmu hP
  have hPb : actualOrdinalNorm (mu+Ordinal.omega0^zeta) ≤ f t := by omega
  have hmub : actualOrdinalNorm mu ≤ f t := by omega
  have hcost : ∀ z : Ordinal.{0}, Ordinal.omega0^zeta ≤ z → z < Ordinal.omega0^E → relativeCost mu z=relativeProfile mu zeta := by
    intro z hPz hzY
    have hzp := hPpos.trans_le hPz
    have hlo := Ordinal.le_log_of_opow_le Ordinal.one_lt_omega0 hPz
    have hhi := (Ordinal.lt_opow_iff_log_lt Ordinal.one_lt_omega0 hzp.ne').mp hzY
    simpa only [relativeCost,if_neg hzp.ne'] using hc _ hlo hhi
  have hmax := relative_maximum_constant_band mu (Ordinal.omega0^E) (Ordinal.omega0^zeta) (f t) (relativeProfile mu zeta)
    hmu hY hP hPpos hPY hmub hPb hcost
  have hnext : descentWith f A-mu=actualMaximumPredecessor (Ordinal.omega0^E) (f t-relativeProfile mu zeta) := by
    unfold descentWith
    rw [hp,hn]
    exact hmax
  have hnon : Ordinal.omega0 ≤ A := (Ordinal.omega0_le_of_isSuccLimit (Ordinal.isSuccLimit_add mu hYl)).trans
    (by rw [← hp]; exact Ordinal.mul_div_le A Ordinal.omega0)
  have hPbudget : actualOrdinalNorm (Ordinal.omega0^zeta) ≤ f t-relativeProfile mu zeta := by omega
  have hkeep : Ordinal.omega0^zeta ≤ descentWith f A-mu := by
    rw [hnext]
    exact (actualMaximumPredecessor_correct _ (Ordinal.opow_pos _ Ordinal.omega0_pos) hY _).2 ⟨hPY,hPbudget⟩
  have hlimkeep := actualLimitPartMonotone hkeep
  have hfixed : actualLimitPart (Ordinal.omega0^zeta)=Ordinal.omega0^zeta := by simpa using limitPart_tail _ hPl 0
  rw [hfixed] at hlimkeep
  exact ⟨hnext,by rw [descent_norm f A hnon hA,hn],hlimkeep,by omega⟩

 theorem actualPureLimitSeparation : Targets.ActualPureLimitSeparation := by
  intro f B hf mu nu E zeta A A' R t hmu hnu hE hz hA hA' hmud hnud hEl hz2 hzE hR hmuR hnuR hER hzR ht hp hp' hn hn' hc hc' hcd
  have h := pure_limit_calibration f B hf mu E zeta A R t hmu hE hz hA hEl hz2 hzE hmuR hzR ht hp hn hc
  have h' := pure_limit_calibration f B hf nu E zeta A' R t hnu hE hz hA' hEl hz2 hzE hnuR hzR ht hp' hn' hc'
  have hu := (G_large t).trans ((selected_threshold_admissible f B hf).2 t)
  have hcR := (relativePrefixNorm mu zeta hmu).2.2.trans hmuR
  have hcR' := (relativePrefixNorm nu zeta hnu).2.2.trans hnuR
  have hlarge := sensitive_tail_double R B t ht
  have hXY : f t-relativeProfile nu zeta < f t-relativeProfile mu zeta := by omega
  have hlogs := (limitLocalTail E hE hEl).2 _ _ h'.2.2.2 hXY
  rw [← h.1,← h'.1] at hlogs
  have hnext := (descent_le f A hA).trans_lt hA
  have hnext' := (descent_le f A' hA').trans_lt hA'
  have hU : descentWith f A-mu < epsilonZero := (Ordinal.sub_le_self _ _).trans_lt hnext
  have hV : descentWith f A'-nu < epsilonZero := (Ordinal.sub_le_self _ _).trans_lt hnext'
  have hzpos : 0 < zeta := (by norm_num : (0 : Ordinal) < 2).trans_le hz2
  have hPnon : Ordinal.omega0 ≤ Ordinal.omega0^zeta := Ordinal.left_le_opow _ hzpos
  have hUnon := (hPnon.trans h.2.2.1).trans (Ordinal.mul_div_le _ _)
  have hVnon := (hPnon.trans h'.2.2.1).trans (Ordinal.mul_div_le _ _)
  rw [phase_limit_log _ hU hUnon,phase_limit_log _ hV hVnon] at hlogs
  have hstrict : actualLimitPart (descentWith f A'-nu) < actualLimitPart (descentWith f A-mu) := by
    by_contra hh
    exact (not_lt_of_ge (Ordinal.log_mono_right Ordinal.omega0 (le_of_not_gt hh))) hlogs
  exact ⟨hstrict,h.2.2.1,h'.2.2.1,h.2.1,h'.2.1⟩

end LogicLineages.PermittedControl
