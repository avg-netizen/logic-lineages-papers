module

public import LogicLineages.ModelsAlgebra.PGroups.PrimeSquareDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.FiniteImageTableDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.UlmDefinitions

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary

def groupPrimeSquareInclusionEvaluation : Prop :=
  ∀ (p : ℕ) (z : ℤ), primeSquareInclusion p (z : ZMod p) = p • (z : ZMod (p ^ 2))

def groupPrimeSquareInclusionInjective : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], Function.Injective (primeSquareInclusion p)

def groupPrimeSquareInclusionRange : Prop :=
  ∀ p : ℕ, (primeSquareInclusion p).range = multipleImage (ZMod (p ^ 2)) p

/-- Actual p-roots for every socle element in the p-squared cyclic group. -/
def groupPrimeSquareSocleRoots : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (z : ZMod (p ^ 2)), p • z = 0 →
    ∃ y : ZMod (p ^ 2), p • y = z

end LogicLineages.ModelsAlgebra.PGroups.Targets
