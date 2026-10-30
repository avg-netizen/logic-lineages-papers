module

public import LogicLineages.ModelsAlgebra.PGroups.UniversalScottTargets
public import LogicLineages.ModelsAlgebra.PGroups.LocallyFiniteScott

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
universe u v

theorem universal_no_scott : Targets.groupUniversalNoScott.{u,v} := by
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
  letI : Finite G := Finite.of_injective e e.injective
  exact not_finite G

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
