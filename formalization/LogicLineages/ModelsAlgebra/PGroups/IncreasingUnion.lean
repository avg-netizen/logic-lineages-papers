module

public import LogicLineages.ModelsAlgebra.PGroups.IncreasingUnionTargets
public import LogicLineages.ModelsAlgebra.PGroups.LocallyFiniteScott

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

open GroupBackAndForth
universe u v

theorem embedding_low_sigma_ascent : Targets.groupEmbeddingLowSigmaAscent.{u,v} := by
  intro β hβ A B _ _ f hf n a φ hφ htruth
  exact (truth_transfer β B A n (fun i => f (a i)) a
    (embedding_low_comparison β hβ A B f hf n a)).2 φ hφ htruth

theorem increasing_tuple_containment : Targets.groupIncreasingTupleContainment.{u} := by
  intro G _ S hmono hcover n
  induction n with
  | zero =>
    intro a
    exact ⟨0, fun i => Fin.elim0 i⟩
  | succ n ih =>
    intro a
    obtain ⟨k, hk⟩ := hcover (a 0)
    obtain ⟨l, hl⟩ := ih (fun i => a i.succ)
    refine ⟨max k l, ?_⟩
    intro i
    exact Fin.cases (hmono (le_max_left k l) hk)
      (fun j => hmono (le_max_right k l) (hl j)) i

private theorem hom_append {A B : Type u} {n m : ℕ} (f : A → B)
    (a : Fin n → A) (c : Fin m → A) :
    (fun i => f (append a c i)) = append (fun i => f (a i)) (fun i => f (c i)) := by
  funext i
  induction i using Fin.addCases <;> simp [append]

private theorem map_empty_append {A B : Type u} {m : ℕ} (f : A → B) (e : Fin m → A) :
    (fun j => f (append (Fin.elim0 : Fin 0 → A) e j)) =
      append (Fin.elim0 : Fin 0 → B) (fun j => f (e j)) := by
  have hnil : (fun j : Fin 0 => f (Fin.elim0 j)) = (Fin.elim0 : Fin 0 → B) := by
    funext j
    exact Fin.elim0 j
  rw [hom_append, hnil]

theorem increasing_pi_two_preservation : Targets.groupIncreasingPiTwoPreservation.{u,v} := by
  intro G _ S hmono hcover φ hφ htruth
  generalize hα : (2 : Ordinal.{v}) = α at hφ
  cases hφ with
  | qf side q => simp at hα
  | pi positive s m matrix β lower rank =>
    intro i d
    obtain ⟨k, hk⟩ := increasing_tuple_containment G S hmono hcover (m i) d
    let e : Fin (m i) → S k := fun j => ⟨d j, hk j⟩
    have below : β i < 2 := by simpa only [← hα] using lower i
    have hstage := embedding_low_sigma_ascent (β i) below (S k) G (S k).subtype
      Subtype.val_injective (0 + m i) (append (Fin.elim0 : Fin 0 → S k) e)
      (matrix i) (rank i) (htruth k i e)
    simpa only [map_empty_append, e, AddSubgroup.coe_subtype] using hstage

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
