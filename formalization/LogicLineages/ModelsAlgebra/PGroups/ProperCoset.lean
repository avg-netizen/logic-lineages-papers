module
public import LogicLineages.ModelsAlgebra.PGroups.ProperCosetTargets
public import LogicLineages.ModelsAlgebra.PGroups.CoprimeFiltration
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe u v

theorem proper_coset_sum_membership : Targets.groupProperCosetSumMembership.{u,v} := by
  intro G _ p hG B x hproper z hz b α
  let S : AddSubgroup G := transfiniteFiltration p α
  change z • x + b ∈ S ↔ x ∈ S ∧ (b : G) ∈ S
  constructor
  · intro h
    have hzmem : z • x ∈ B ⊔ S := by
      have hm := (B ⊔ S).sub_mem
        ((le_sup_right : S ≤ B ⊔ S) h)
        ((le_sup_left : B ≤ B ⊔ S) b.property)
      simpa only [add_sub_cancel_right] using hm
    have hxmem := (coprime_subgroup_membership G p hG (B ⊔ S) z hz x).mp hzmem
    obtain ⟨c,hc,y,hy,hcy⟩ := AddSubgroup.mem_sup.mp hxmem
    have he : x + -c = y := by
      rw [← hcy, add_right_comm, add_neg_cancel, zero_add]
    have hxS : x ∈ S := hproper ⟨-c,B.neg_mem hc⟩ α (by
      change x + -c ∈ S
      rw [he]
      exact hy)
    refine ⟨hxS,?_⟩
    simpa only [add_sub_cancel_left] using S.sub_mem h (S.zsmul_mem hxS z)
  · rintro ⟨hx,hb⟩
    exact S.add_mem (S.zsmul_mem hx z) hb

end LogicLineages.ModelsAlgebra.PGroups
