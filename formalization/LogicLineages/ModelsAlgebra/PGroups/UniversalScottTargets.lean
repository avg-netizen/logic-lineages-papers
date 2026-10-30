module

public import LogicLineages.ModelsAlgebra.PGroups.ScottDefinitions
public import Mathlib.SetTheory.Ordinal.Arithmetic

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
universe u v

/-- Paper01's universal Scott obstruction via the actual bottom subgroup.
No local finiteness or p-primary hypothesis is needed. -/
def groupUniversalNoScott : Prop :=
  ∀ (G : Type u) [AddCommGroup G] [Countable G] [Infinite G]
    (φ : Formula 0), Complexity .pi (1 : Ordinal.{v}) φ →
      ¬ GroupScottSentence G φ

end LogicLineages.ModelsAlgebra.PGroups.Targets
