module

public import LogicLineages.ModelsAlgebra.PGroups.AnnihilationDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.ScottDefinitions
public import Mathlib.SetTheory.Ordinal.Arithmetic

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
universe u v

/-- The literal universal sentence every element is zero is Scott for
an actual trivial group in the additive-group model domain. -/
def groupTrivialPiOneScott : Prop :=
  Complexity .pi (1 : Ordinal.{v}) (annihilationFormula 1 0) ∧
    ∀ (G : Type u) [AddCommGroup G] [Subsingleton G],
      GroupScottSentence G (annihilationFormula 1 0)

end LogicLineages.ModelsAlgebra.PGroups.Targets
