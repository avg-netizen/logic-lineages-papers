module
public import LogicLineages.ModelsAlgebra.PGroups.ReducedPrueferComparisonDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupBackAndForth
def reducedPrueferComparison : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Countable G] (p : ℕ) [Fact p.Prime],
    (∀ x:G, ∃ k:ℕ, p^k • x=0) → IsReducedAddGroup G →
    ∀ γ : Ordinal.{0}, StagesNonzeroBelow p G (Ordinal.omega0*γ) →
    ∀ (n:ℕ) (a:Fin n→G),
      BackAndForth (2*γ) a (fun i=>(a i,(0:PrueferModel p)))
end LogicLineages.ModelsAlgebra.PGroups.Targets
