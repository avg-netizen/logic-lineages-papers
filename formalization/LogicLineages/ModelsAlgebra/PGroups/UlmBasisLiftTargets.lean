module

public import LogicLineages.ModelsAlgebra.PGroups.UlmDefinitions
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Data.Nat.Prime.Defs

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

/-- Actual quotient bases, actual representatives and actual cyclic roots.
No independence/spanning/decomposition property is built into these data. -/
def groupUlmBasisLiftExistence : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G],
    ∃ (I : ℕ → Type)
      (b : ∀ j, Module.Basis (I j) (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup G)))
      (x : ∀ j, I j → pSocle p (finiteFiltration p j : AddSubgroup G))
      (y : ∀ j, I j → G),
      ∀ (j : ℕ) (i : I j),
        QuotientAddGroup.mk' (successorSocleSubgroup p (finiteFiltration p j)) (x j i) = b j i ∧
        p ^ j • y j i = (x j i : G) ∧ p ^ (j + 1) • y j i = 0

end LogicLineages.ModelsAlgebra.PGroups.Targets
