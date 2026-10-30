module

public import LogicLineages.ModelsAlgebra.PGroups.LocallyFiniteScottTargets
public import LogicLineages.ModelsAlgebra.PGroups.Infinitary
public import LogicLineages.ModelsAlgebra.PGroups.BackForthCore

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

open GroupBackAndForth
universe u v

private theorem hom_append {A B : Type u} {n m : ℕ} (f : A → B)
    (a : Fin n → A) (c : Fin m → A) :
    (fun i => f (append a c i)) = append (fun i => f (a i)) (fun i => f (c i)) := by
  funext i
  induction i using Fin.addCases <;> simp [append]

theorem embedding_low_comparison : Targets.groupEmbeddingLowBackForth.{u,v} := by
  intro β hβ A B _ _ f hf n a
  by_cases hzero : β = 0
  · subst β
    apply (zero_comparison B A n _ a).mpr
    intro s t
    exact (embedding_atomic_agreement A B f hf n a s t).symm
  · apply (positive_comparison β hzero B A n _ a).mpr
    intro γ hγ m d
    have hγzero : γ = 0 := Order.lt_one_iff.mp (lt_of_lt_of_le hγ (Order.lt_two_iff.mp hβ))
    subst γ
    refine ⟨fun i => f (d i), (zero_comparison A B (n + m) _ _).mpr ?_⟩
    simpa only [hom_append] using embedding_atomic_agreement A B f hf (n + m) (append a d)

theorem embedding_low_pi_descent : Targets.groupEmbeddingLowPiDescent.{u,v} := by
  intro β hβ A B _ _ f hf n a φ hφ htruth
  exact (truth_transfer β B A n (fun i => f (a i)) a
    (embedding_low_comparison β hβ A B f hf n a)).1 φ hφ htruth

theorem sigma_two_finite_submodel : Targets.groupSigmaTwoFiniteSubmodel.{u,v} := by
  intro G _ hfinite φ hφ htruth
  generalize hα : (2 : Ordinal.{v}) = α at hφ
  cases hφ with
  | qf side q => simp at hα
  | sigma positive s m matrix β lower rank =>
    obtain ⟨i, d, hd⟩ := htruth
    let S : AddSubgroup G := AddSubgroup.closure (Set.range d)
    let e : Fin (m i) → S := fun j => ⟨d j, AddSubgroup.subset_closure ⟨j, rfl⟩⟩
    refine ⟨S, hfinite (m i) d, i, e, ?_⟩
    have below : β i < 2 := by simpa only [← hα] using lower i
    apply embedding_low_pi_descent (β i) below S G S.subtype Subtype.val_injective
      (0 + m i) (append (Fin.elim0 : Fin 0 → S) e) (matrix i) (rank i)
    have hnil : (fun j : Fin 0 => S.subtype (Fin.elim0 j)) = (Fin.elim0 : Fin 0 → G) := by
      funext j
      exact Fin.elim0 j
    have hmap : (fun j => S.subtype (append (Fin.elim0 : Fin 0 → S) e j)) =
        append (Fin.elim0 : Fin 0 → G) d := by
      rw [hom_append, hnil]
      rfl
    simpa only [hmap] using hd

theorem locally_finite_no_sigma_two_scott : Targets.groupLocallyFiniteNoSigmaTwoScott.{u,v} := by
  intro G _ _ _ hfinite φ hφ hScott
  obtain ⟨S, hS, htruth⟩ := sigma_two_finite_submodel G hfinite φ hφ hScott.1
  letI : Fintype S := hS.fintype
  obtain ⟨e⟩ := hScott.2 S htruth
  letI : Finite G := Finite.of_injective e e.injective
  exact not_finite G

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
