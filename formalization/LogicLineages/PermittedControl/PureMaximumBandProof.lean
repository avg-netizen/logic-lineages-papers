module
public import LogicLineages.PermittedControl.PureSuccessorTargets
public import LogicLineages.PermittedControl.ProfileBandReturnProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem relative_maximum_constant_band (mu rho P : Ordinal.{0}) (b c : Nat)
    (hmu : mu < epsilonZero) (hrho : rho < epsilonZero) (hP : P < epsilonZero)
    (hPpos : 0 < P) (hPrho : P < rho)
    (hmub : actualOrdinalNorm mu ≤ b) (hPb : actualOrdinalNorm (mu+P) ≤ b)
    (hcost : ∀ z : Ordinal.{0}, P ≤ z → z < rho → relativeCost mu z=c) :
    relativeMaximum mu rho b=actualMaximumPredecessor rho (b-c) := by
  have hrhopos := hPpos.trans hPrho
  have hrel := relativeMaximumSpec mu rho b (epsilonZero_add_principal hmu hrho) hrhopos hmub
  have hNR : actualOrdinalNorm P+c ≤ b := by
    have h := (relativeNorm mu P hmu hP).1
    rw [hcost P le_rfl hPrho] at h
    omega
  have hc : c ≤ b := by omega
  have hsmall := actualMaximumPredecessor_correct rho hrhopos hrho (b-c)
  have hPsmall : P ≤ actualMaximumPredecessor rho (b-c) := hsmall.2 ⟨hPrho,by omega⟩
  have hPrel : P ≤ relativeMaximum mu rho b := hrel.2.2 ⟨hPrho,by rwa [hcost P le_rfl hPrho]⟩
  apply le_antisymm
  · apply hsmall.2
    refine ⟨hrel.2.1.1,?_⟩
    have hh := hrel.2.1.2
    rw [hcost _ hPrel hrel.2.1.1] at hh
    omega
  · apply hrel.2.2
    refine ⟨hsmall.1.1,?_⟩
    rw [hcost _ hPsmall hsmall.1.1]
    have hh := hsmall.1.2
    omega

 theorem pure_quotient_large (R B t u c v : Nat) (ht : thickBlockTail R B ≤ t)
    (hu : 2*t+4 ≤ u) (hc : c ≤ R) (hv : 0 < v) (hvR : v ≤ R+1) :
    R+2 < (u-c)/v := by
  have ht4 : 100*(R+2)^4 ≤ t := (le_max_left _ _).trans ht
  have h24 : (R+2)^2 ≤ (R+2)^4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hprod : (R+3)*v ≤ 2*(R+2)^4 := by
    have h := Nat.mul_le_mul (show R+3 ≤ 2*(R+2) by omega) (show v ≤ R+2 by omega)
    have hh : (R+3)*v ≤ 2*((R+2)^2) := by simpa only [Nat.pow_two,Nat.mul_assoc] using h
    exact hh.trans (Nat.mul_le_mul_left 2 h24)
  have hR4 : R+2 ≤ (R+2)^4 := Nat.le_self_pow (by omega : 4 ≠ 0) (R+2)
  have hX : 2*(R+2)^4 ≤ u-c := by omega
  have hq : R+3 ≤ (u-c)/v := (Nat.le_div_iff_mul_le hv).mpr (hprod.trans hX)
  omega

 theorem pure_successor_maximum (mu beta : Ordinal.{0}) (b : Nat)
    (hmu : mu < epsilonZero) (hb : beta < epsilonZero)
    (hmub : actualOrdinalNorm mu ≤ b)
    (hPb : actualOrdinalNorm (mu+Ordinal.omega0^beta) ≤ b) :
    relativeMaximum mu (Ordinal.omega0^(beta+1)) b=
      actualMaximumPredecessor (Ordinal.omega0^(beta+1)) (b-relativeProfile mu beta) := by
  have hbs : beta+1 < epsilonZero := by simpa using (actualFiniteTailClosureNorm beta hb 1).1
  have hP := phase_power_below beta hb
  have hY := phase_power_below (beta+1) hbs
  have hPY := (Ordinal.isNormal_opow Ordinal.one_lt_omega0).strictMono (show beta < beta+1 from Order.lt_add_one_iff.mpr le_rfl)
  apply relative_maximum_constant_band mu _ _ b _ hmu hY hP (Ordinal.opow_pos _ Ordinal.omega0_pos) hPY hmub hPb
  intro z hPz hzY
  have hlog : Ordinal.log Ordinal.omega0 (Ordinal.omega0^beta)=beta := Ordinal.log_opow Ordinal.one_lt_omega0 beta
  have hh := retained_band_cost mu (Ordinal.omega0^beta) z (Ordinal.opow_pos _ Ordinal.omega0_pos) hPz (by rwa [hlog])
  simpa only [hlog] using hh

end LogicLineages.PermittedControl
