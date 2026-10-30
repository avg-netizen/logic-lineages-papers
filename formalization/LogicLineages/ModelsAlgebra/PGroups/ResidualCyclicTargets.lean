module
public import LogicLineages.ModelsAlgebra.PGroups.ResidualCyclicDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary

def groupResidualCyclicExponent : Prop :=
  ∀ (p N : ℕ) (I : Fin N → Type) (a b : Fin N) (x : ResidualCyclicProduct p N I a b),
    p ^ N • x = 0

def groupResidualCyclicRank : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N : ℕ) (I : Fin N → Type) (a b j : Fin N),
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j.val :
      AddSubgroup (ResidualCyclicProduct p N I a b))) =
      if j = a ∨ j = b then 0 else Cardinal.mk (I j)

end LogicLineages.ModelsAlgebra.PGroups.Targets
