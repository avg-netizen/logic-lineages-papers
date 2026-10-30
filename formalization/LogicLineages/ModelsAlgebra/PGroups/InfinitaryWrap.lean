module

public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryWrapTargets
public import LogicLineages.ModelsAlgebra.PGroups.CountableBranches

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

open GroupBackAndForth
universe u v

private theorem append_empty {G : Type u} {n : ℕ} (a : Fin n → G) (d : Fin 0 → G) :
    append a d = a := by
  funext i
  simpa [append] using (Fin.addCases_left (m := n) (n := 0) (motive := fun _ => G)
    (left := a) (right := d) i)

theorem sigma_wrap_realization : Targets.groupSigmaWrapRealization.{u} := by
  intro G _ n φ a
  unfold sigmaWrap
  rw [countable_disj_ex_realization Unit n _ _ G a]
  constructor
  · rintro ⟨i, d, hd⟩
    simpa only [append_empty] using hd
  · intro h
    exact ⟨(), Fin.elim0, by simpa only [append_empty] using h⟩

theorem pi_wrap_realization : Targets.groupPiWrapRealization.{u} := by
  intro G _ n φ a
  unfold piWrap
  rw [countable_conj_all_realization Unit n _ _ G a]
  constructor
  · intro h
    simpa only [append_empty] using h () Fin.elim0
  · intro h i d
    simpa only [append_empty] using h

theorem sigma_wrap_complexity : Targets.groupSigmaWrapComplexity.{v} := by
  intro α β hα hβ n φ hφ
  exact countable_disj_ex_complexity α hα Unit n (fun _ => 0) (fun _ => φ)
    (fun _ => β) (fun _ => hβ) (fun _ => hφ)

theorem pi_wrap_complexity : Targets.groupPiWrapComplexity.{v} := by
  intro α β hα hβ n φ hφ
  exact countable_conj_all_complexity α hα Unit n (fun _ => 0) (fun _ => φ)
    (fun _ => β) (fun _ => hβ) (fun _ => hφ)

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
