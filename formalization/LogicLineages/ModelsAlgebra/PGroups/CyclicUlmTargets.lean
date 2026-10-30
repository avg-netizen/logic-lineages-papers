module

public import LogicLineages.ModelsAlgebra.PGroups.CyclicSocleTargets
public import Mathlib.LinearAlgebra.Dimension.Finite

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

/-- Actual surviving quotient with its existing ZMod action. -/
def groupCyclicTopUlmIsomorphism : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), 0 < k →
    Nonempty (UlmLayer p (finiteFiltration p (k - 1) : AddSubgroup (ZMod (p ^ k)))
      ≃ₗ[ZMod p] ZMod p)

/-- Genuine cardinal dimension of the actual cyclic Ulm quotient, including
length zero and all finite filtration indices. -/
def groupCyclicUlmRank : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k j : ℕ),
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j : AddSubgroup (ZMod (p ^ k)))) =
      if j + 1 = k then 1 else 0

end LogicLineages.ModelsAlgebra.PGroups.Targets
