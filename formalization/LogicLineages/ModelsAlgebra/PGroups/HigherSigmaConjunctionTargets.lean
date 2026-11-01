module
public import LogicLineages.ModelsAlgebra.PGroups.SigmaTwoConjunctionDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
/-- The existing literal branch-pairing syntax works at every common rank
at least2. The source orbit/collapse use has rank2*gamma with gamma>0. -/
def higherSigmaConjunctionComplexity : Prop :=
  ∀ α:Ordinal.{0}, 2≤α → ∀ (n:ℕ) (φ ψ:Formula n),
    Complexity .sigma α φ → Complexity .sigma α ψ →
    Complexity .sigma α (sigmaTwoConjunction φ ψ)
end LogicLineages.ModelsAlgebra.PGroups.Targets
