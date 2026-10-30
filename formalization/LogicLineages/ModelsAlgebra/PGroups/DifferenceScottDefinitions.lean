module

public import LogicLineages.ModelsAlgebra.PGroups.ScottDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.ImageCardinalityDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryWrapDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.SigmaTwoConjunctionDefinitions

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
universe u

/-- Relative Scott truth and categoricity, including all finite countable models. -/
def DifferenceScottSentence (G : Type u) [AddCommGroup G] (d : DifferenceFormula 0) : Prop :=
  d.Realize (Fin.elim0 : Fin 0 → G) ∧
    ∀ (H : Type u) [AddCommGroup H] [Countable H],
      d.Realize (Fin.elim0 : Fin 0 → H) → Nonempty (G ≃+ H)

noncomputable def differenceSigmaTwo {n : ℕ} (d : DifferenceFormula n) : Formula n :=
  sigmaTwoConjunction d.sigmaPart (sigmaWrap d.piPart)

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
