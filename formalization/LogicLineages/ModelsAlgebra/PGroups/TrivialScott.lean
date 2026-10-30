module

public import LogicLineages.ModelsAlgebra.PGroups.TrivialScottTargets
public import LogicLineages.ModelsAlgebra.PGroups.Annihilation

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
universe u v

theorem trivial_pi_one_scott : Targets.groupTrivialPiOneScott.{u,v} := by
  constructor
  · exact (annihilation_formula.{0,v} 1 0).1
  · intro G _ _
    constructor
    · apply ((annihilation_formula.{u,0} 1 0).2 G Fin.elim0).mpr
      intro x
      exact Subsingleton.elim _ _
    · intro H _ _ hH
      have hzero : ∀ x : H, x = 0 := by
        intro x
        simpa only [one_nsmul] using
          (((annihilation_formula.{u,0} 1 0).2 H Fin.elim0).mp hH) x
      refine ⟨AddEquiv.ofBijective (0 : G →+ H) ⟨?_, ?_⟩⟩
      · intro x y h
        exact Subsingleton.elim _ _
      · intro y
        exact ⟨0, (hzero y).symm⟩

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
