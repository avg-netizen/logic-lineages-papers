module

public import LogicLineages.ModelsAlgebra.PGroups.BackForthCoreTargets
public import LogicLineages.ModelsAlgebra.PGroups.BackForth

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.GroupBackAndForth

universe u v

theorem term_hom_evaluation : Targets.groupTermHomEvaluation.{u} := by
  intro A B _ _ f n a t
  induction t with
  | var i => rfl
  | zero => exact f.map_zero
  | neg s ih => simpa only [GroupTerm.eval, map_neg] using congrArg (fun x : B => -x) ih
  | add s t ihs iht =>
    simpa only [GroupTerm.eval, map_add] using congrArg₂ (fun x y : B => x + y) ihs iht

theorem embedding_atomic_agreement : Targets.groupEmbeddingAtomicAgreement.{u} := by
  intro A B _ _ f hf n a s t
  rw [← term_hom_evaluation A B f n a s, ← term_hom_evaluation A B f n a t]
  exact hf.eq_iff.symm

theorem comparison_reflexive : Targets.groupBackForthReflexive.{u,v} := by
  intro α
  induction α using WellFoundedLT.induction with
  | ind α ih =>
    intro A _ n a
    by_cases hα : α = 0
    · subst α
      rw [zero_comparison A A n a a]
      intro s t
      exact Iff.rfl
    · apply (positive_comparison α hα A A n a a).mpr
      intro β hβ m d
      exact ⟨d, ih β hβ A (n + m) (append a d)⟩

theorem comparison_transitive : Targets.groupBackForthTransitive.{u,v} := by
  intro α
  induction α using WellFoundedLT.induction with
  | ind α ih =>
    intro A B C _ _ _ n a b c hab hbc
    by_cases hα : α = 0
    · subst α
      have ha := (zero_comparison A B n a b).mp hab
      have hb := (zero_comparison B C n b c).mp hbc
      apply (zero_comparison A C n a c).mpr
      intro s t
      exact (ha s t).trans (hb s t)
    · apply (positive_comparison α hα A C n a c).mpr
      intro β hβ m d
      obtain ⟨dB, hCB⟩ := (positive_comparison α hα B C n b c).mp hbc β hβ m d
      obtain ⟨dA, hBA⟩ := (positive_comparison α hα A B n a b).mp hab β hβ m dB
      exact ⟨dA, ih β hβ C B A (n + m) (append c d) (append b dB) (append a dA) hCB hBA⟩

private theorem map_append {A B : Type u} {n m : ℕ} (f : A → B)
    (a : Fin n → A) (c : Fin m → A) :
    (fun i => f (append a c i)) = append (fun i => f (a i)) (fun i => f (c i)) := by
  funext i
  induction i using Fin.addCases <;> simp [append]

theorem comparison_isomorphism : Targets.groupBackForthIsomorphism.{u,v} := by
  intro α
  induction α using WellFoundedLT.induction with
  | ind α ih =>
    intro A B _ _ f n a
    by_cases hα : α = 0
    · subst α
      apply (zero_comparison A B n a (fun i => f (a i))).mpr
      exact embedding_atomic_agreement A B f.toAddMonoidHom f.injective n a
    · apply (positive_comparison α hα A B n a (fun i => f (a i))).mpr
      intro β hβ m d
      refine ⟨fun i => f.symm (d i), ?_⟩
      have hh := ih β hβ B A f.symm (n + m) (append (fun i => f (a i)) d)
      rw [map_append] at hh
      simpa only [AddEquiv.symm_apply_apply] using hh

end LogicLineages.ModelsAlgebra.PGroups.GroupBackAndForth
