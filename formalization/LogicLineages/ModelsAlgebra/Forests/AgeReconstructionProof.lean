module

public import LogicLineages.ModelsAlgebra.Forests.AgeReconstructionTargets
public import Mathlib.Tactic.FinCases

/-! Forest axioms are finite-local. The actual relational age supplies every
finite patch, including the empty one, so the resulting carrier is a forest. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.AgeReconstructionProof

open FirstOrder AgeConstruction

theorem finitePatchesForestOrder : Targets.FinitePatchesForestOrder := by
  classical
  intro α R hp
  have hr : ∀ x, R x x := by
    intro x
    obtain ⟨F, f, hf⟩ := hp {x}
    let a : {t : α // t ∈ ({x} : Finset α)} := ⟨x, by simp⟩
    exact (hf a a).mp le_rfl
  have ht : ∀ x y z, R x y → R y z → R x z := by
    intro x y z hxy hyz
    obtain ⟨F, f, hf⟩ := hp {x, y, z}
    let a : {t : α // t ∈ ({x, y, z} : Finset α)} := ⟨x, by simp⟩
    let b : {t : α // t ∈ ({x, y, z} : Finset α)} := ⟨y, by simp⟩
    let c : {t : α // t ∈ ({x, y, z} : Finset α)} := ⟨z, by simp⟩
    exact (hf a c).mp (le_trans ((hf a b).mpr hxy) ((hf b c).mpr hyz))
  have ha : ∀ x y, R x y → R y x → x = y := by
    intro x y hxy hyx
    obtain ⟨F, f, hf⟩ := hp {x, y}
    let a : {t : α // t ∈ ({x, y} : Finset α)} := ⟨x, by simp⟩
    let b : {t : α // t ∈ ({x, y} : Finset α)} := ⟨y, by simp⟩
    exact congrArg Subtype.val (f.injective
      (le_antisymm ((hf a b).mpr hxy) ((hf b a).mpr hyx)))
  let po : PartialOrder α := {
    le := R
    lt := fun x y => R x y ∧ ¬ R y x
    le_refl := hr
    le_trans := ht
    le_antisymm := ha
    lt_iff_le_not_ge := fun _ _ => Iff.rfl }
  refine ⟨po, ?_, fun _ _ => Iff.rfl⟩
  intro x y z hx hy
  obtain ⟨F, f, hf⟩ := hp {x, y, z}
  let a : {t : α // t ∈ ({x, y, z} : Finset α)} := ⟨x, by simp⟩
  let b : {t : α // t ∈ ({x, y, z} : Finset α)} := ⟨y, by simp⟩
  let c : {t : α // t ∈ ({x, y, z} : Finset α)} := ⟨z, by simp⟩
  rcases F.forest ((hf a c).mpr hx) ((hf b c).mpr hy) with h | h
  · exact Or.inl ((hf a b).mp h)
  · exact Or.inr ((hf b a).mp h)

theorem forestModelAgeFinitePatches : Targets.ForestModelAgeFinitePatches := by
  classical
  intro K M hAge s
  let S := Language.Substructure.closure Language.order (s : Set M)
  let N : OrderModel := CategoryTheory.Bundled.of S
  have hN : N ∈ Language.order.age M :=
    ⟨(Language.Substructure.fg_iff_structure_fg S).mp
      (Language.Substructure.fg_closure s.finite_toSet), ⟨S.subtype⟩⟩
  rw [hAge] at hN
  obtain ⟨F, _, ⟨e⟩⟩ := hN
  let incl : {x : M // x ∈ s} ↪ S := {
    toFun := fun x => ⟨x.val, Language.Substructure.subset_closure x.property⟩
    inj' := fun x y h => Subtype.ext (congrArg (fun z : S => (z : M)) h) }
  let f : {x : M // x ∈ s} ↪ F.Carrier := {
    toFun := fun x => e.symm (incl x)
    inj' := e.symm.injective.comp incl.injective }
  refine ⟨F, f, ?_⟩
  intro x y
  have he := e.symm.map_rel .le ![incl x, incl y]
  change f x ≤ f y ↔ @Language.Structure.RelMap Language.order M M.str 2
    Language.orderRel.le (fun i => ((![incl x, incl y] i : S) : M)) at he
  have hv : (fun i => ((![incl x, incl y] i : S) : M)) = ![x.val, y.val] := by
    ext i
    fin_cases i <;> rfl
  rw [hv] at he
  exact he

theorem countableForestModelReconstruction : Targets.CountableForestModelReconstruction := by
  intro K M hcount hAge
  obtain ⟨po, hforest, hrel⟩ := finitePatchesForestOrder M (modelLE M)
    (forestModelAgeFinitePatches K M hAge)
  let A : CountableOrderForest := {
    Carrier := M
    carrierPartialOrder := po
    carrierCountable := hcount
    forest := hforest }
  refine ⟨A, ⟨{
    toEquiv := _root_.Equiv.refl M
    map_fun' := fun f => isEmptyElim f
    map_rel' := ?_ }⟩⟩
  intro n r v
  cases r
  have hv : ![v 0, v 1] = v := by
    ext i
    fin_cases i <;> rfl
  change @Language.Structure.RelMap Language.order M M.str 2 Language.orderRel.le v ↔
    @LE.le M po.toLE (v 0) (v 1)
  rw [hrel]
  unfold modelLE
  exact iff_of_eq (congrArg (fun w : Fin 2 → M =>
    @Language.Structure.RelMap Language.order M M.str 2 Language.orderRel.le w) hv).symm

end LogicLineages.ModelsAlgebra.Forests.AgeReconstructionProof
