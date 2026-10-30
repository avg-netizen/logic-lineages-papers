module

public import LogicLineages.ModelsAlgebra.PGroups.CyclicSplittingTargets
public import LogicLineages.ModelsAlgebra.PGroups.BoundedExtension
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem bounded_cyclic_retraction : Targets.groupBoundedCyclicRetraction := by
  intro n _ G _ hbound i hi
  let e := AddMonoidHom.ofInjective hi
  obtain ⟨r,hr⟩ := bounded_cyclic_extension n G hbound i.range e.symm.toAddMonoidHom
  refine ⟨r, ?_⟩
  intro a
  have ha := hr (e a)
  change r (i a) = e.symm (e a) at ha
  simpa only [e.symm_apply_apply] using ha

theorem retraction_kernel_product : Targets.groupRetractionKernelProduct := by
  intro A G _ _ i r hri
  let q : G →+ r.ker :=
    { toFun := fun x => ⟨x - i (r x), by
        change r (x - i (r x)) = 0
        rw [map_sub, hri, sub_self]⟩
      map_zero' := by apply Subtype.ext; simp
      map_add' := by
        intro x y
        apply Subtype.ext
        change (x + y) - i (r (x + y)) = (x - i (r x)) + (y - i (r y))
        rw [map_add, map_add]
        abel }
  let f := r.prod q
  apply Nonempty.intro (AddEquiv.ofBijective f ?_)
  constructor
  · intro x y h
    have h₁ : r x = r y := congrArg Prod.fst h
    have h₂ : x - i (r x) = y - i (r y) :=
      congrArg (fun z : A × r.ker => (z.2 : G)) h
    rw [h₁] at h₂
    simpa only [sub_left_inj] using h₂
  · rintro ⟨a,b⟩
    refine ⟨i a + (b : G), ?_⟩
    apply Prod.ext
    · change r (i a + (b : G)) = a
      rw [map_add, hri, b.property, add_zero]
    · apply Subtype.ext
      change i a + (b : G) - i (r (i a + (b : G))) = (b : G)
      rw [map_add, hri, b.property, add_zero]
      abel

theorem maximal_cyclic_splitting : Targets.groupMaximalCyclicSplitting := by
  classical
  intro n _ G _ hbound y hy
  let S := AddSubgroup.zmultiples y
  let sy : S := ⟨y, ⟨1, one_zsmul y⟩⟩
  have hgen : ∀ x : S, x ∈ AddSubgroup.zmultiples sy := by
    intro x
    obtain ⟨a,ha⟩ := x.property
    exact ⟨a, Subtype.ext ha⟩
  have hcard : Nat.card S = n := (Nat.card_zmultiples y).trans hy
  let e : ZMod n ≃+ S := zmodAddEquivOfGenerator hgen hcard
  let i : ZMod n →+ G := S.subtype.comp e.toAddMonoidHom
  have hi : Function.Injective i := Subtype.val_injective.comp e.injective
  obtain ⟨r,hr⟩ := bounded_cyclic_retraction n G hbound i hi
  have hi1 : i 1 = y := by
    exact congrArg (fun x : S => (x : G)) (zmodAddEquivOfGenerator_apply_one hgen hcard)
  refine ⟨r, ?_, retraction_kernel_product (ZMod n) G i r hr⟩
  rw [← hi1]
  exact hr 1

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
