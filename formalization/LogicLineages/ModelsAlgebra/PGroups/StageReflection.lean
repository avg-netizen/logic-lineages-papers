module
public import LogicLineages.ModelsAlgebra.PGroups.StageReflectionTargets
public import LogicLineages.ModelsAlgebra.PGroups.IncreasingUnion
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
open GroupBackAndForth

private theorem hom_append {A B : Type} {n m : ℕ} (f : A → B)
    (a : Fin n → A) (c : Fin m → A) :
    (fun i => f (append a c i)) = append (fun i => f (a i)) (fun i => f (c i)) := by
  funext i
  induction i using Fin.addCases <;> simp [append]

private theorem map_empty_append {A B : Type} {m : ℕ} (f : A → B) (d : Fin m → A) :
    (fun j => f (append (Fin.elim0 : Fin 0 → A) d j)) =
      append (Fin.elim0 : Fin 0 → B) (fun j => f (d j)) := by
  have hnil : (fun j : Fin 0 => f (Fin.elim0 j)) = (Fin.elim0 : Fin 0 → B) := by
    funext j
    exact Fin.elim0 j
  rw [hom_append, hnil]

theorem pi_two_tuple_retract_reflection : Targets.groupPiTwoTupleRetractReflection := by
  intro G H _ _ i _ hfix φ hφ ht
  generalize hα : (2 : Ordinal.{0}) = α at hφ
  cases hφ with
  | qf side q => simp at hα
  | pi positive s m matrix β lower rank =>
    intro b d
    obtain ⟨f,hf,hfd⟩ := hfix (m b) d
    have below : β b < 2 := by simpa only [← hα] using lower b
    have h := embedding_low_sigma_ascent (β b) below G H f hf (0+m b)
      (append (Fin.elim0 : Fin 0 → G) (fun j => i (d j))) (matrix b) (rank b)
      (ht b (fun j => i (d j)))
    have he : (fun j => f (i (d j))) = d := funext hfd
    simpa only [map_empty_append, he] using h

theorem difference_two_stage_reflection : Targets.groupDifferenceTwoStageReflection := by
  intro G _ S hmono hcover hfix d hlevel ht
  rcases d with ⟨σ,π⟩
  rcases hlevel with ⟨hσ,hπ⟩
  rcases ht with ⟨hσt,hπt⟩
  generalize hα : (2 : Ordinal.{0}) = α at hσ
  cases hσ with
  | qf side q => simp at hα
  | sigma positive s m matrix β lower rank =>
    obtain ⟨b,d,hd⟩ := hσt
    obtain ⟨k,hk⟩ := increasing_tuple_containment G S hmono hcover (m b) d
    let e : Fin (m b) → S k := fun j => ⟨d j,hk j⟩
    refine ⟨k, ?_, pi_two_tuple_retract_reflection G (S k) (S k).subtype
      Subtype.val_injective (hfix k) π hπ hπt⟩
    refine ⟨b,e,?_⟩
    have below : β b < 2 := by simpa only [← hα] using lower b
    apply embedding_low_pi_descent (β b) below (S k) G (S k).subtype Subtype.val_injective
      (0+m b) (append (Fin.elim0 : Fin 0 → S k) e) (matrix b) (rank b)
    simpa only [map_empty_append, e, AddSubgroup.coe_subtype] using hd

theorem chain_no_difference_two_scott : Targets.groupChainNoDifferenceTwoScott := by
  intro G _ _ S hmono hcover hfix hnon d hd hs
  obtain ⟨k,hk⟩ := difference_two_stage_reflection G S hmono hcover hfix d hd hs.1
  letI : Countable (S k) := Subtype.val_injective.countable
  exact hnon k (hs.2 (S k) hk)

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
