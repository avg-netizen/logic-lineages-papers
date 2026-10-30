module

public import LogicLineages.ModelsAlgebra.Forests.ThickeningTargets
public import Lean.Elab.Tactic.Omega

/-! Actual finite chain subdivisions of a forest template. Maximal points are
exactly original leaves at the last chain coordinate, so width is preserved. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.ThickeningProof

theorem thickeningPartialOrderLaws : Targets.ThickeningPartialOrderLaws := by
  intro T n
  refine ⟨fun x => ⟨le_rfl, fun _ => le_rfl⟩, ?_, ?_⟩
  · intro x y z hxy hyz
    refine ⟨le_trans hxy.1 hyz.1, fun heq => ?_⟩
    have hxyEq : x.1 = y.1 := le_antisymm hxy.1 (by rw [heq]; exact hyz.1)
    have hyzEq : y.1 = z.1 := hxyEq.symm.trans heq
    exact le_trans (hxy.2 hxyEq) (hyz.2 hyzEq)
  · intro x y hxy hyx
    have heq : x.1 = y.1 := le_antisymm hxy.1 hyx.1
    exact Prod.ext heq (le_antisymm (hxy.2 heq) (hyx.2 heq.symm))

theorem thickeningPredecessorsChain : Targets.ThickeningPredecessorsChain := by
  classical
  intro T n x y z hx hy
  by_cases heq : x.1 = y.1
  · rcases le_total x.2 y.2 with h | h
    · exact Or.inl ⟨heq.le, fun _ => h⟩
    · exact Or.inr ⟨heq.ge, fun _ => h⟩
  · rcases T.forest hx.1 hy.1 with h | h
    · exact Or.inl ⟨h, fun hEq => False.elim (heq hEq)⟩
    · exact Or.inr ⟨h, fun hEq => False.elim (heq hEq.symm)⟩

theorem thickeningMaximalPoints : Targets.ThickeningMaximalPoints := by
  intro T n x
  constructor
  · intro hx
    constructor
    · intro y hxy
      exact (hx (y, x.2) ⟨hxy, fun _ => le_rfl⟩).1
    · intro j
      rcases le_total x.2 j with h | h
      · exact (hx (x.1, j) ⟨le_rfl, fun _ => h⟩).2 rfl
      · exact h
  · rintro ⟨hx, hj⟩ y hxy
    exact ⟨hx hxy.1, fun _ => hj y.2⟩

theorem actualFiniteThickening : Targets.ActualFiniteThickening := by
  classical
  intro T n hn
  let po : PartialOrder (T.Carrier × Fin n) := {
    le := thickLE T n
    lt := fun x y => thickLE T n x y ∧ ¬ thickLE T n y x
    lt_iff_le_not_ge := fun _ _ => Iff.rfl
    le_refl := (thickeningPartialOrderLaws T n).1
    le_trans := (thickeningPartialOrderLaws T n).2.1
    le_antisymm := (thickeningPartialOrderLaws T n).2.2 }
  let H : FiniteOrderForest := {
    Carrier := T.Carrier × Fin n
    carrierFintype := inferInstance
    carrierPartialOrder := po
    forest := fun {x y z} hx hy => thickeningPredecessorsChain T n x y z hx hy }
  let top : Fin n := ⟨n - 1, by omega⟩
  have htop (j : Fin n) : j ≤ top := by
    change j.val ≤ n - 1
    omega
  let f : ForestLeaf T → ForestLeaf H := fun ℓ =>
    ⟨(ℓ.val, top), (thickeningMaximalPoints T n (ℓ.val, top)).mpr ⟨ℓ.property, htop⟩⟩
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun ℓ : ForestLeaf H => ℓ.val.1) hab
  have hsurj : Function.Surjective f := by
    intro ℓ
    have hx := (thickeningMaximalPoints T n ℓ.val).mp ℓ.property
    have heq : top = ℓ.val.2 := le_antisymm (hx.2 top) (htop ℓ.val.2)
    refine ⟨⟨ℓ.val.1, hx.1⟩, ?_⟩
    apply Subtype.ext
    exact Prod.ext rfl heq
  refine ⟨H, Equiv.refl _, fun _ _ => Iff.rfl, ?_⟩
  have hcard := Fintype.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  simpa only [Fintype.card_subtype, leafFinset] using hcard.symm

end LogicLineages.ModelsAlgebra.Forests.ThickeningProof
