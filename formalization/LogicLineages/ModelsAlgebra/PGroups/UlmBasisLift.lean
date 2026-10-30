module

public import LogicLineages.ModelsAlgebra.PGroups.UlmBasisLiftTargets
public import LogicLineages.ModelsAlgebra.PGroups.UlmFiniteIndependence
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

theorem ulm_basis_lift_existence : Targets.groupUlmBasisLiftExistence := by
  classical
  intro p _ G _
  letI : ∀ j : ℕ, Module.Free (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G)) :=
    fun j => Module.Free.of_divisionRing (ZMod p) _
  let I (j : ℕ) := Module.Free.ChooseBasisIndex (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G))
  let b (j : ℕ) : Module.Basis (I j) (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G)) :=
    Module.Free.chooseBasis (ZMod p) _
  have hreps : ∀ (j : ℕ) (i : I j), ∃ x : pSocle p (finiteFiltration p j : AddSubgroup G),
      QuotientAddGroup.mk' (successorSocleSubgroup p (finiteFiltration p j)) x = b j i := by
    intro j i
    exact QuotientAddGroup.mk'_surjective _ (b j i)
  choose x hx using hreps
  have hroots : ∀ (j : ℕ) (i : I j), ∃ y : G, p ^ j • y = (x j i : G) := by
    intro j i
    have hm := (x j i).property.1
    exact (finite_filtration_multiple_image G p j).le hm
  choose y hy using hroots
  refine ⟨I, b, x, y, ?_⟩
  intro j i
  refine ⟨hx j i, hy j i, ?_⟩
  rw [pow_succ', mul_smul, hy]
  exact (x j i).property.2

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
