module
public import LogicLineages.ModelsAlgebra.PGroups.PrimarySocleControlTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

theorem primary_socle_injectivity : Targets.primarySocleInjectivity := by
  intro p G H _ _ hp f hi
  have hz : ∀ k : ℕ, ∀ x : G, p^k • x=0 → f x=0 → x=0 := by
    intro k
    induction k with
    | zero => intro x hx _; simpa only [pow_zero,one_nsmul] using hx
    | succ k ih =>
      intro x hx hfx
      have hpx : p • x=0 := ih (p • x)
        (by simpa only [pow_succ',mul_nsmul] using hx)
        (by rw [map_nsmul,hfx,nsmul_zero])
      have hh := hi (a₁:=⟨x,AddSubgroup.mem_top _,hpx⟩) (a₂:=0)
        (hfx.trans f.map_zero.symm)
      exact congrArg Subtype.val hh
  intro x y h
  obtain ⟨k,hk⟩ := hp (x-y)
  apply sub_eq_zero.mp
  apply hz k (x-y) hk
  rw [map_sub,h,sub_self]

theorem primary_divisible_socle_surjectivity : Targets.primaryDivisibleSocleSurjectivity := by
  intro p G D _ _ hp hG hd f hs
  have hsur : ∀ k : ℕ, ∀ x : G, p^k • x=0 → ∃ y:D, f y=x := by
    intro k
    induction k with
    | zero =>
      intro x hx
      have hx0 : x=0 := by simpa only [pow_zero,one_nsmul] using hx
      exact ⟨0,f.map_zero.trans hx0.symm⟩
    | succ k ih =>
      intro x hx
      obtain ⟨a,ha⟩ := ih (p • x) (by simpa only [pow_succ',mul_nsmul] using hx)
      obtain ⟨b,hb⟩ := hd p hp a
      have hpx : p • (x-f b)=0 := by
        rw [nsmul_sub,←map_nsmul,hb,ha,sub_self]
      obtain ⟨c,hc⟩ := hs ⟨x-f b,AddSubgroup.mem_top _,hpx⟩
      refine ⟨c+b,?_⟩
      rw [map_add,hc,sub_add_cancel]
  intro x
  obtain ⟨k,hk⟩ := hG x
  exact hsur k x hk
end LogicLineages.ModelsAlgebra.PGroups
