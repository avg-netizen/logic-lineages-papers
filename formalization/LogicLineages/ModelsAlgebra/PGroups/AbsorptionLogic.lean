module
public import LogicLineages.ModelsAlgebra.PGroups.AbsorptionLogicTargets
public import LogicLineages.ModelsAlgebra.PGroups.LocallyFiniteScott
public import LogicLineages.ModelsAlgebra.PGroups.IncreasingUnion
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
open GroupBackAndForth

private theorem hom_append {A B : Type} {n m : ℕ} (f : A → B)
    (a : Fin n → A) (c : Fin m → A) :
    (fun j => f (append a c j)) = append (fun j => f (a j)) (fun j => f (c j)) := by
  funext j
  induction j using Fin.addCases <;> simp [append]

theorem tuple_fixing_sigma_one : Targets.groupTupleFixingSigmaOne := by
  intro G H _ _ i hi hfix n a φ hφ
  constructor
  · exact embedding_low_sigma_ascent 1 (by simp) H G i hi n a φ hφ
  · intro ht
    obtain ⟨f,hf,hfa⟩ := hfix n a
    have h := embedding_low_sigma_ascent 1 (by simp) G H f hf n (fun j => i (a j)) φ hφ ht
    have he : (fun j => f (i (a j))) = a := funext hfa
    simpa only [he] using h

theorem tuple_fixing_backforth_one : Targets.groupTupleFixingBackForthOne := by
  intro G H _ _ i _ hfix n a
  apply (positive_comparison 1 one_ne_zero H G n a _).mpr
  intro β hβ m d
  have hz : β = 0 := Order.lt_one_iff.mp hβ
  subst β
  obtain ⟨f,hf,hfa⟩ := hfix n a
  refine ⟨fun j => f (d j), (zero_comparison G H (n+m) _ _).mpr ?_⟩
  have he : (fun j => f (i (a j))) = a := funext hfa
  simpa only [hom_append, he] using
    embedding_atomic_agreement G H f hf (n+m) (append (fun j => i (a j)) d)

theorem tuple_fixing_backforth_two : Targets.groupTupleFixingBackForthTwo := by
  intro G H _ _ i hi hfix
  apply (positive_comparison 2 (by simp) G H 0 Fin.elim0 Fin.elim0).mpr
  intro β hβ m d
  refine ⟨fun j => i (d j), ?_⟩
  have he : (fun j => i (append (Fin.elim0 : Fin 0 → H) d j)) =
      append (Fin.elim0 : Fin 0 → G) (fun j => i (d j)) := by
    rw [hom_append]
    congr 1
    funext j
    exact Fin.elim0 j
  by_cases hz : β = 0
  · subst β
    apply (zero_comparison H G (0+m) _ _).mpr
    simpa only [he] using embedding_atomic_agreement H G i hi (0+m) (append Fin.elim0 d)
  · have ho : β = 1 := le_antisymm (Order.lt_two_iff.mp hβ) (Order.one_le_iff_ne_zero.mpr hz)
    subst β
    simpa only [he] using tuple_fixing_backforth_one G H i hi hfix (0+m) (append Fin.elim0 d)

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
