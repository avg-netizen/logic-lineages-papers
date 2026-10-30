module

public import LogicLineages.ModelsAlgebra.PGroups.ScottDefinitions
public import Mathlib.SetTheory.Ordinal.Arithmetic

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
universe u v

def groupNontrivialNoPiOneScott : Prop :=
  ∀ (G : Type u) [AddCommGroup G] [Countable G] [Nontrivial G]
    (φ : Formula 0), Complexity .pi (1 : Ordinal.{v}) φ → ¬ GroupScottSentence G φ

def groupFiniteNoSigmaOneScott : Prop :=
  ∀ (G : Type u) [AddCommGroup G] [Countable G] [Finite G]
    (φ : Formula 0), Complexity .sigma (1 : Ordinal.{v}) φ → ¬ GroupScottSentence G φ

end LogicLineages.ModelsAlgebra.PGroups.Targets
