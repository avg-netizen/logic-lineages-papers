module

public import LogicLineages.ModelsAlgebra.PGroups.FiniteScottLowerTargets
public import LogicLineages.ModelsAlgebra.PGroups.LocallyFiniteScott
public import LogicLineages.ModelsAlgebra.PGroups.IncreasingUnion
public import Mathlib.Algebra.Group.Prod

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
universe u v

theorem nontrivial_no_pi_one_scott : Targets.groupNontrivialNoPiOneScott.{u,v} := by
  intro G _ _ _ φ hφ hs
  let S : AddSubgroup G := ⊥
  have he : (fun i : Fin 0 => S.subtype (Fin.elim0 i)) = (Fin.elim0 : Fin 0 → G) := by
    funext i
    exact Fin.elim0 i
  have htruth : φ.Realize (Fin.elim0 : Fin 0 → S) := by
    apply embedding_low_pi_descent 1 (by simp) S G S.subtype Subtype.val_injective 0
      Fin.elim0 φ hφ
    simpa only [he] using hs.1
  obtain ⟨e⟩ := hs.2 S htruth
  letI : Subsingleton G := e.injective.subsingleton
  exact false_of_nontrivial_of_subsingleton G

theorem finite_no_sigma_one_scott : Targets.groupFiniteNoSigmaOneScott.{u,v} := by
  intro G _ _ _ φ hφ hs
  let f : G →+ G × ℤ :=
    { toFun := fun x => (x, 0)
      map_zero' := rfl
      map_add' := fun x y => by simp }
  have hf : Function.Injective f := fun x y h => congrArg Prod.fst h
  have he : (fun i : Fin 0 => f (Fin.elim0 i)) = (Fin.elim0 : Fin 0 → G × ℤ) := by
    funext i
    exact Fin.elim0 i
  have htruth : φ.Realize (Fin.elim0 : Fin 0 → G × ℤ) := by
    simpa only [he] using embedding_low_sigma_ascent 1 (by simp) G (G × ℤ) f hf 0
      Fin.elim0 φ hφ hs.1
  obtain ⟨e⟩ := hs.2 (G × ℤ) htruth
  letI : Finite (G × ℤ) := Finite.of_surjective e e.surjective
  exact not_finite (G × ℤ)

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
