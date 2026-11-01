module
public import LogicLineages.ModelsAlgebra.PGroups.ShortStableScottTargets
public import LogicLineages.ModelsAlgebra.PGroups.StableTailScottProof
public import LogicLineages.ModelsAlgebra.PGroups.ReducedLengthProof
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleProductComparisonProof
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupInfinitary

theorem short_stable_scott_upper : Targets.shortStableScottUpper := by
  intro p _ G _ _ γ _ α hcount hprimary hαγ hstable
  obtain ⟨z,hz,_⟩ := countable_length_normal_form α hcount
  letI : Countable z.1.ToType := hz.1
  have hβγ : z.1 < γ := by
    by_contra h
    have hm : Ordinal.omega0*γ ≤ Ordinal.omega0*z.1 :=
      mul_le_mul_left' (le_of_not_gt h) Ordinal.omega0
    exact (not_le_of_gt hαγ) (hm.trans (by rw [hz.2]; exact le_self_add))
  have ht : StableAt p (transfiniteFiltration p (Ordinal.omega0*z.1) : AddSubgroup G)
      (z.2:Ordinal.{0}) := by
    apply AddSubgroup.ext
    intro x
    change x ∈ (transfiniteFiltration p (z.2:Ordinal.{0}) :
      AddSubgroup (transfiniteFiltration p (Ordinal.omega0*z.1) : AddSubgroup G)) ↔
      x ∈ (transfiniteFiltration p ((z.2:Ordinal.{0})+1) :
      AddSubgroup (transfiniteFiltration p (Ordinal.omega0*z.1) : AddSubgroup G))
    rw [transfinite_tail_membership,transfinite_tail_membership,←add_assoc,←hz.2]
    exact SetLike.ext_iff.mp hstable (x:G)
  obtain ⟨φ,hφ,hs⟩ := stable_tail_scott_upper p G z.1 z.2 hprimary ht
  have hlevel : 2*z.1+3 ≤ 2*γ+1 := by
    have hm : 2*z.1+2 ≤ (2:Ordinal.{0})*γ := by
      have hh := mul_le_mul_left' (Order.succ_le_of_lt hβγ) (2:Ordinal.{0})
      simpa only [Order.succ_eq_add_one,mul_add_one] using hh
    simpa only [Order.succ_eq_add_one,add_assoc,
      show (2:Ordinal.{0})+1=3 from by norm_num] using Order.succ_le_succ hm
  exact ⟨φ,positive_complexity_monotone .pi (2*z.1+3) (2*γ+1) 0 φ
    (by positivity) hlevel hφ,hs⟩

theorem short_reduced_product_scott_upper : Targets.shortReducedProductScottUpper := by
  intro p _ R D _ _ _ _ γ _ ell hcount hR hD _ hd hlen hlt
  obtain ⟨hprimary,hmem,_⟩ := divisible_product_data R D p hR hD hd
  have hz : (transfiniteFiltration p (ell+1) : AddSubgroup R)=⊥ := by
    apply le_antisymm _ bot_le
    exact (transfiniteFiltration_antitone p (show ell≤ell+1 from le_self_add)).trans
      (le_of_eq hlen.1)
  have hstable : StableAt p (R×D) ell := by
    apply AddSubgroup.ext
    intro x
    rw [hmem ell x,hmem (ell+1) x,hlen.1,hz]
  exact short_stable_scott_upper p (R×D) γ ell hcount hprimary hlt hstable

end LogicLineages.ModelsAlgebra.PGroups
