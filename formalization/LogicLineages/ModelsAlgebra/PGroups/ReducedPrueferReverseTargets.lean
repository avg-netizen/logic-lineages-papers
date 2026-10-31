module
public import LogicLineages.ModelsAlgebra.PGroups.ReducedPrueferReverseDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupBackAndForth
def reducedPrueferReverse : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Countable G] (p : ℕ) [Fact p.Prime],
    (∀ x:G, ∃ k:ℕ, p^k • x=0) → IsReducedAddGroup G →
    ∀ γ : Ordinal.{0}, StagesNonzeroBelow p G (Ordinal.omega0*γ) →
    ∀ (n:ℕ) (a:Fin n→G),
      BackAndForth (2*γ) (fun i=>(a i,(0:PrueferModel p))) a
end LogicLineages.ModelsAlgebra.PGroups.Targets
