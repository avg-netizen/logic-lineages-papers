module
public import LogicLineages.ModelsAlgebra.PGroups.CutAmalgamationTargets
public import Mathlib.Algebra.Group.Prod
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe u v

theorem cut_amalgamation : Targets.cutAmalgamation.{u,v} := by
  classical
  intro G H _ _ p δ B L f g _ hg hL hBL hdeep hagree hpres
  let E := B ⊔ L
  let π : B × L →+ E := {
    toFun := fun x => ⟨(x.1:G)+x.2, E.add_mem ((le_sup_left : B ≤ E) x.1.property)
      ((le_sup_right : L ≤ E) x.2.property)⟩
    map_zero' := by apply Subtype.ext; exact zero_add 0
    map_add' := by intro x y; apply Subtype.ext; exact add_add_add_comm _ _ _ _ }
  have hπ : Function.Surjective π := by
    intro x
    obtain ⟨b,hb,l,hl,hx⟩ := AddSubgroup.mem_sup.mp x.property
    exact ⟨(⟨b,hb⟩,⟨l,hl⟩),Subtype.ext hx⟩
  let s : B × L →+ H := {
    toFun := fun x => f x.1 + g x.2
    map_zero' := by simp
    map_add' := by intro x y; simp only [Prod.fst_add,Prod.snd_add,map_add]; exact add_add_add_comm _ _ _ _ }
  have hker : π.ker ≤ s.ker := by
    intro x hx
    have hx' : (x.1:G)+(x.2:G)=0 := congrArg Subtype.val hx
    have hb : (x.1:G) ∈ L := by rw [eq_neg_of_add_eq_zero_left hx']; exact L.neg_mem x.2.property
    change f x.1 + g x.2 = 0
    rw [hagree x.1 x.1.property hb,← map_add]
    have hz : (⟨(x.1:G),hb⟩ : L)+x.2=0 := Subtype.ext hx'
    rw [hz,map_zero]
  let F : E →+ H := π.liftOfSurjective hπ ⟨s,hker⟩
  have hF (b : B) (l : L) : F (π (b,l)) = f b + g l := by
    exact π.liftOfRightInverse_comp_apply (Function.surjInv hπ)
      (Function.rightInverse_surjInv hπ) ⟨s,hker⟩ (b,l)
  have hz (x : E) (hx : F x=0) : x=0 := by
    obtain ⟨⟨b,l⟩,rfl⟩ := hπ x
    rw [hF] at hx
    have hfb : f b ∈ (transfiniteFiltration p δ : AddSubgroup H) := by
      rw [eq_neg_of_add_eq_zero_left hx]
      exact (transfiniteFiltration p δ).neg_mem (hdeep l)
    have hb : (b:G) ∈ L := hBL ⟨b.property,(hpres b δ le_rfl).mp hfb⟩
    rw [hagree b b.property hb,← map_add,← map_zero g] at hx
    have he := congrArg Subtype.val (hg hx)
    exact Subtype.ext he
  have hi : Function.Injective F := by
    intro x y h
    exact sub_eq_zero.mp (hz (x-y) (by rw [map_sub,h,sub_self]))
  refine ⟨F,hi,?_,?_,?_⟩
  · intro b
    have he : π (b,0) = ⟨b,(le_sup_left : B ≤ E) b.property⟩ := Subtype.ext (add_zero _)
    rw [← he]
    simpa only [map_zero,add_zero] using hF b 0
  · intro l
    have he : π (0,l) = ⟨l,(le_sup_right : L ≤ E) l.property⟩ := Subtype.ext (zero_add _)
    rw [← he]
    simpa only [map_zero,zero_add] using hF 0 l
  · intro x β hβ
    obtain ⟨⟨b,l⟩,rfl⟩ := hπ x
    rw [hF]
    have hl := transfiniteFiltration_antitone p hβ (hL l.property)
    have hgl := transfiniteFiltration_antitone p hβ (hdeep l)
    change f b+g l ∈ (transfiniteFiltration p β : AddSubgroup H) ↔
      (b:G)+(l:G) ∈ (transfiniteFiltration p β : AddSubgroup G)
    constructor
    · intro h
      exact (transfiniteFiltration p β).add_mem
        ((hpres b β hβ).mp (by simpa only [add_sub_cancel_right] using
          (transfiniteFiltration p β : AddSubgroup H).sub_mem h hgl)) hl
    · intro h
      exact (transfiniteFiltration p β).add_mem
        ((hpres b β hβ).mpr (by simpa only [add_sub_cancel_right] using
          (transfiniteFiltration p β : AddSubgroup G).sub_mem h hl)) hgl
end LogicLineages.ModelsAlgebra.PGroups
