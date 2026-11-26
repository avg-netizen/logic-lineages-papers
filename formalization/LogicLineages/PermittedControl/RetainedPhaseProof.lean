module
public import LogicLineages.PermittedControl.LocalTailProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem retained_prefix_cost (mu P a x : Ordinal.{0}) (hmu : mu < epsilonZero)
    (hP : P < epsilonZero) (ha : a < epsilonZero) (hPpos : 0 < P)
    (hdiv : Ordinal.omega0^a ∣ P) (hx : x < Ordinal.omega0^a) :
    actualOrdinalNorm (P+x) = actualOrdinalNorm P + actualOrdinalNorm x ∧
    relativeCost mu (P+x) = relativeProfile mu (Ordinal.log Ordinal.omega0 P) := by
  have hxbelow := hx.trans (phase_power_below a ha)
  have hxbound : x < Ordinal.omega0^(a+1) := hx.trans_le
    ((Ordinal.isNormal_opow Ordinal.one_lt_omega0).monotone (le_self_add : a ≤ a+1))
  have hnorm := (actualDivisiblePrefixNormAddition P x hP hxbelow a hdiv hxbound).2
  have haE : a ≤ Ordinal.log Ordinal.omega0 P := Ordinal.le_log_of_opow_le
    Ordinal.one_lt_omega0 (Ordinal.le_of_dvd hPpos.ne' hdiv)
  have hE : P < Ordinal.omega0^(Ordinal.log Ordinal.omega0 P+1) :=
    Ordinal.lt_opow_of_log_lt Ordinal.one_lt_omega0 (Order.lt_add_one_iff.mpr le_rfl)
  have hxE : x < Ordinal.omega0^(Ordinal.log Ordinal.omega0 P+1) := hx.trans_le
    ((Ordinal.isNormal_opow Ordinal.one_lt_omega0).monotone (haE.trans le_self_add))
  have hsum := Ordinal.isPrincipal_add_omega0_opow (Ordinal.log Ordinal.omega0 P+1) hE hxE
  have hnon : P+x ≠ 0 := (hPpos.trans_le le_self_add).ne'
  have hlog : Ordinal.log Ordinal.omega0 (P+x) = Ordinal.log Ordinal.omega0 P := by
    apply le_antisymm
    · exact Order.lt_add_one_iff.mp ((Ordinal.lt_opow_iff_log_lt Ordinal.one_lt_omega0 hnon).mp hsum)
    · exact Ordinal.log_mono_right _ le_self_add
  exact ⟨hnorm, by simp [relativeCost, hnon, hlog]⟩

 theorem retainedLocalPhase : Targets.RetainedLocalPhase := by
  intro mu P a b hmu hP ha hPpos hapos hdiv hmub hbudget
  let c := relativeProfile mu (Ordinal.log Ordinal.omega0 P)
  let X := b-c-actualOrdinalNorm P
  let w := actualMaximumPredecessor (Ordinal.omega0^a) X
  let R := relativeMaximum mu (P+Ordinal.omega0^a) b
  have hpw := phase_power_below a ha
  have hrho := epsilonZero_add_principal hP hpw
  have habsolute := epsilonZero_add_principal hmu hrho
  have hmax := actualMaximumPredecessor_correct (Ordinal.omega0^a)
    (Ordinal.opow_pos a Ordinal.omega0_pos) hpw X
  have hgreat := (relativeMaximumSpec mu (P+Ordinal.omega0^a) b habsolute
    (hPpos.trans_le le_self_add) hmub).2
  have hw : w < Ordinal.omega0^a := hmax.1.1
  have hwcost := retained_prefix_cost mu P a w hmu hP ha hPpos hdiv hw
  have hcandidate : P+w ≤ R := by
    apply hgreat.2
    refine ⟨(add_lt_add_iff_left P).mpr hw, ?_⟩
    rw [hwcost.1, hwcost.2]
    have hN : actualOrdinalNorm w ≤ X := hmax.1.2
    dsimp [X,c] at hN
    omega
  have hPR : P ≤ R := (le_self_add : P ≤ P+w).trans hcandidate
  have hx : R-P < Ordinal.omega0^a :=
    (Ordinal.sub_lt_of_le hPR).mpr hgreat.1.1
  have hR : R = P+(R-P) := (Ordinal.add_sub_cancel_of_le hPR).symm
  have hcost := retained_prefix_cost mu P a (R-P) hmu hP ha hPpos hdiv hx
  have hN : actualOrdinalNorm (R-P) ≤ X := by
    have hb := hgreat.1.2
    change actualOrdinalNorm R + relativeCost mu R ≤ b at hb
    rw [hR, hcost.1, hcost.2] at hb
    dsimp [X,c]
    omega
  have hupper : R ≤ P+w := by
    rw [hR]
    exact (add_le_add_iff_left P).mpr (hmax.2 ⟨hx,hN⟩)
  exact le_antisymm hupper hcandidate

end LogicLineages.PermittedControl
