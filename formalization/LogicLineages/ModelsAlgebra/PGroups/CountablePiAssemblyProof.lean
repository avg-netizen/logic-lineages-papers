module
public import LogicLineages.ModelsAlgebra.PGroups.CountablePiAssemblyTargets
public import LogicLineages.ModelsAlgebra.PGroups.CountableBranches
public import Mathlib.Data.Countable.Basic
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
open GroupInfinitary
universe u

theorem countable_pi_assembly : Targets.countablePiAssembly.{u} := by
  classical
  intro α hα ι _ n φ hφ
  have hparts (i : ι) : ∃ (s : Set ℕ) (m : s → ℕ) (matrix : ∀ j, Formula (n+m j))
      (β : s → Ordinal.{0}), φ i = .conjAll s m matrix ∧
        (∀ j, β j < α) ∧ (∀ j, Complexity .sigma (β j) (matrix j)) := by
    have h := hφ i
    generalize he : φ i = χ at h
    cases h with
    | qf side q => exact (hα rfl).elim
    | pi positive s m matrix β lower rank => exact ⟨s,m,matrix,β,rfl,lower,rank⟩
  choose s m matrix β heq lower rank using hparts
  let I := Σ i : ι, s i
  let ψ : Formula n := countableConjAll (ι := I) (fun z => m z.1 z.2) (fun z => matrix z.1 z.2)
  refine ⟨ψ,countable_conj_all_complexity α hα I n _ _ (fun z => β z.1 z.2)
    (fun z => lower z.1 z.2) (fun z => rank z.1 z.2),?_⟩
  intro G _ a
  rw [countable_conj_all_realization]
  constructor
  · intro h i
    rw [heq i]
    exact fun j d => h ⟨i,j⟩ d
  · intro h z d
    have hi := h z.1
    rw [heq z.1] at hi
    exact hi z.2 d
end LogicLineages.ModelsAlgebra.PGroups
