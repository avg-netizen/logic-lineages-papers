module
public import LogicLineages.PermittedControl.PropagationTargets
public import LogicLineages.PermittedControl.RelativeTrajectoryProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

private theorem nonfinite_of_positive_limit (u : Ordinal.{0}) (h : 0 < actualLimitPart u) :
    Ordinal.omega0 ≤ u := by
  by_contra hn
  obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp (lt_of_not_ge hn)
  rw [limitPart_finite] at h
  exact (lt_irrefl 0) h

private theorem relative_bound (mu u : Ordinal.{0}) (h : mu+u < epsilonZero) :
    mu+actualLimitPart u < epsilonZero :=
  (add_le_add_right (Ordinal.mul_div_le u Ordinal.omega0) mu).trans_lt h

 theorem strictPropagation : Targets.StrictPropagation := by
  intro mu nu u v S b c b' hu hv hmuS hnuS hub hmc hpos hgap hbudget
  have huBelow : u < epsilonZero := (le_add_self : u ≤ mu+u).trans_lt hu
  have hvBelow : v < epsilonZero := (le_add_self : v ≤ nu+v).trans_lt hv
  have hnuBelow : nu < epsilonZero := (le_self_add : nu ≤ nu+v).trans_lt hv
  have hdu := actualNonfiniteDecomposition u (nonfinite_of_positive_limit u hpos) huBelow
  have hnormrho : actualOrdinalNorm (actualLimitPart u) ≤ b := by
    have hn := hdu.2.2.2
    omega
  have hnub : actualOrdinalNorm nu ≤ b' := by omega
  have hlo := (relativeMaximumSpec mu (actualLimitPart u) c (relative_bound mu u hu) hpos hmc).2
  have hhi := (relativeMaximumSpec nu (actualLimitPart v) b' (relative_bound nu v hv)
    (hpos.trans hgap) hnub).2
  have hcost : relativeCost nu (actualLimitPart u) ≤ S :=
    (relativeNorm nu (actualLimitPart u) hnuBelow hdu.1).2.2 |>.trans hnuS
  have hcandidate : actualLimitPart u ≤ relativeMaximum nu (actualLimitPart v) b' :=
    hhi.2 ⟨hgap, by omega⟩
  have hproj := actualLimitPartMonotone hcandidate
  have hfixed : actualLimitPart (actualLimitPart u) = actualLimitPart u := by
    simpa using limitPart_tail (actualLimitPart u) hdu.2.1 0
  rw [hfixed] at hproj
  exact ⟨hproj, (Ordinal.mul_div_le _ Ordinal.omega0).trans_lt hlo.1.1⟩

 theorem weakPropagation : Targets.WeakPropagation := by
  intro mu nu u v S c b' hu hv hmuS hnuS hmc hpos heq hbudget
  have hnub : actualOrdinalNorm nu ≤ b' := by omega
  have hlo := (relativeMaximumSpec mu (actualLimitPart u) c (relative_bound mu u hu) hpos hmc).2
  have hhi := (relativeMaximumSpec nu (actualLimitPart v) b' (relative_bound nu v hv)
    (by rwa [heq]) hnub).2
  have hbelow : relativeMaximum mu (actualLimitPart u) c < epsilonZero :=
    (hlo.1.1.trans_le (Ordinal.mul_div_le u Ordinal.omega0)).trans
      ((le_add_self : u ≤ mu+u).trans_lt hu)
  have hcost : relativeCost nu (relativeMaximum mu (actualLimitPart u) c) ≤ S :=
    (relativeNorm nu _ ((le_self_add : nu ≤ nu+v).trans_lt hv) hbelow).2.2 |>.trans hnuS
  apply actualLimitPartMonotone
  apply hhi.2
  refine ⟨by rw [heq]; exact hlo.1.1, ?_⟩
  have hc := hlo.1.2
  omega

 theorem orderedProfilePropagation : Targets.OrderedProfilePropagation := by
  intro mu nu u v c hu hv hmc hnc hpos heq hcost
  have hlo := (relativeMaximumSpec mu (actualLimitPart u) c (relative_bound mu u hu) hpos hmc).2
  have hhi := (relativeMaximumSpec nu (actualLimitPart v) c (relative_bound nu v hv)
    (by rwa [heq]) hnc).2
  apply actualLimitPartMonotone
  apply hhi.2
  refine ⟨by rw [heq]; exact hlo.1.1, ?_⟩
  exact (Nat.add_le_add_left (hcost _ hlo.1.1) _).trans hlo.1.2

 theorem propagation : Targets.Propagation :=
  ⟨strictPropagation, weakPropagation, orderedProfilePropagation⟩

end LogicLineages.PermittedControl
