module

public import LogicLineages.ModelsAlgebra.PGroups.CountableBranchesTargets

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

open GroupBackAndForth
universe u v

theorem countable_disj_ex_realization : Targets.groupCountableDisjExRealization.{u} := by
  intro ι _ n m matrix G _ a
  let e := branchEquiv ι
  change (∃ k : branchIndices ι, ∃ d : Fin (m (e.symm k)) → G,
    (matrix (e.symm k)).Realize (append a d)) ↔ _
  constructor
  · rintro ⟨k, d, hd⟩
    exact ⟨e.symm k, d, hd⟩
  · rintro ⟨i, d, hd⟩
    refine ⟨e i, ?_⟩
    rw [e.symm_apply_apply i]
    exact ⟨d, hd⟩

theorem countable_conj_all_realization : Targets.groupCountableConjAllRealization.{u} := by
  intro ι _ n m matrix G _ a
  let e := branchEquiv ι
  change (∀ k : branchIndices ι, ∀ d : Fin (m (e.symm k)) → G,
    (matrix (e.symm k)).Realize (append a d)) ↔ _
  constructor
  · intro h i
    have hi := h (e i)
    rw [e.symm_apply_apply i] at hi
    exact hi
  · intro h k d
    exact h (e.symm k) d

theorem countable_disj_ex_complexity : Targets.groupCountableDisjExComplexity.{v} := by
  intro α hα ι _ n m matrix β lower rank
  exact Complexity.sigma hα (branchIndices ι)
    (fun k => m ((branchEquiv ι).symm k)) (fun k => matrix ((branchEquiv ι).symm k))
    (fun k => β ((branchEquiv ι).symm k))
    (fun k => lower ((branchEquiv ι).symm k)) (fun k => rank ((branchEquiv ι).symm k))

theorem countable_conj_all_complexity : Targets.groupCountableConjAllComplexity.{v} := by
  intro α hα ι _ n m matrix β lower rank
  exact Complexity.pi hα (branchIndices ι)
    (fun k => m ((branchEquiv ι).symm k)) (fun k => matrix ((branchEquiv ι).symm k))
    (fun k => β ((branchEquiv ι).symm k))
    (fun k => lower ((branchEquiv ι).symm k)) (fun k => rank ((branchEquiv ι).symm k))

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
