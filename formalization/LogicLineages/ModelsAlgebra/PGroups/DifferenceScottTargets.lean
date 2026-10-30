module

public import LogicLineages.ModelsAlgebra.PGroups.DifferenceScottDefinitions
public import Mathlib.SetTheory.Ordinal.Arithmetic

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
universe u v

def groupDifferenceSigmaTwoRealization : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (n : ℕ) (d : DifferenceFormula n) (a : Fin n → G),
    (differenceSigmaTwo d).Realize a ↔ d.Realize a

def groupDifferenceSigmaTwoComplexity : Prop :=
  ∀ (n : ℕ) (d : DifferenceFormula n), d.AtLevel (1 : Ordinal.{v}) →
    Complexity .sigma (2 : Ordinal.{v}) (differenceSigmaTwo d)

/-- The source's d-Sigma-one obstruction, relative to a larger class than
p-groups and therefore also obstructing unrestricted Scott categoricity. -/
def groupLocallyFiniteNoDifferenceOneScott : Prop :=
  ∀ (G : Type u) [AddCommGroup G] [Countable G] [Infinite G], LocallyFinite G →
    ∀ d : DifferenceFormula 0, d.AtLevel (1 : Ordinal.{v}) →
      ¬ DifferenceScottSentence G d

end LogicLineages.ModelsAlgebra.PGroups.Targets
