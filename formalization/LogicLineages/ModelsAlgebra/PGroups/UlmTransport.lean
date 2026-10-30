module
public import LogicLineages.ModelsAlgebra.PGroups.UlmTransportTargets
public import Mathlib.Algebra.Module.Submodule.Equiv
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem injective_socle_map : Targets.groupInjectiveSocleMap := by
  intro G H _ _ p S f hf
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨⟨x,hx.1,rfl⟩, ?_⟩
    change p • f x = 0
    have hz : p • x = 0 := hx.2
    rw [← map_nsmul, hz, map_zero]
  · rintro ⟨⟨x,hx,rfl⟩,hy⟩
    refine ⟨x, ⟨hx, ?_⟩,rfl⟩
    apply hf
    change f (p • x) = f 0
    rw [map_nsmul, map_zero]
    exact hy

private theorem step_map (G H : Type) [AddCommGroup G] [AddCommGroup H]
    (p : ℕ) (S : AddSubgroup G) (f : G →+ H) :
    pStep p (S.map f) = (pStep p S).map f := by
  ext y
  constructor
  · rintro ⟨z,⟨x,hx,rfl⟩,rfl⟩
    refine ⟨p • x,⟨x,hx,rfl⟩,?_⟩
    exact map_nsmul f p x
  · rintro ⟨z,⟨x,hx,rfl⟩,rfl⟩
    refine ⟨f x,⟨x,hx,rfl⟩,?_⟩
    exact (map_nsmul f p x).symm

theorem injective_ulm_isomorphism : Targets.groupInjectiveUlmIsomorphism := by
  classical
  intro G H _ _ p S f hf
  let T := S.map f
  let coord : pSocle p S → pSocle p T := fun x =>
    ⟨f x, (injective_socle_map G H p S f hf).le ⟨x,x.property,rfl⟩⟩
  let q : pSocle p S →+ UlmLayer p T :=
    { toFun := fun x => QuotientAddGroup.mk' (successorSocleSubgroup p T) (coord x)
      map_zero' := by
        change QuotientAddGroup.mk' _ (coord 0) = 0
        have hz : coord 0 = 0 := Subtype.ext (map_zero f)
        rw [hz,map_zero]
      map_add' := by
        intro x y
        have ha : coord (x+y) = coord x + coord y := Subtype.ext (map_add f (x : G) (y : G))
        change QuotientAddGroup.mk' _ (coord (x+y)) = _
        rw [ha,map_add] }
  have hs : Function.Surjective q := by
    intro z
    obtain ⟨y,rfl⟩ := QuotientAddGroup.mk'_surjective (successorSocleSubgroup p T) z
    obtain ⟨x,hx,hxy⟩ := (injective_socle_map G H p S f hf).ge y.property
    refine ⟨⟨x,hx⟩, ?_⟩
    have he : coord ⟨x,hx⟩ = y := Subtype.ext hxy
    change QuotientAddGroup.mk' _ (coord ⟨x,hx⟩) = _
    rw [he]
  have hn : pSocle p (pStep p T) = (pSocle p (pStep p S)).map f := by
    rw [show T = S.map f from rfl, step_map, ← injective_socle_map G H p (pStep p S) f hf]
  have hk : successorSocleSubgroup p S = q.ker := by
    ext x
    change (x.val ∈ pSocle p (pStep p S)) ↔ q x = 0
    rw [show q x = 0 ↔ coord x ∈ successorSocleSubgroup p T from
      QuotientAddGroup.eq_zero_iff (coord x)]
    change _ ↔ f x.val ∈ pSocle p (pStep p T)
    rw [hn, AddSubgroup.mem_map_iff_mem hf]
  let e := QuotientAddGroup.liftEquiv _ hs hk
  exact ⟨LinearEquiv.ofBijective (e.toAddMonoidHom.toZModLinearMap p) e.bijective⟩

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
