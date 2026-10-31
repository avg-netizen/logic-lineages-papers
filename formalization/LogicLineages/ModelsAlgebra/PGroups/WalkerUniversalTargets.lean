module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerUniversalDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

/-- Genuine presentation universal property of the recursively constructed
finite quotient, supplying rather than assuming every homomorphism. -/
def walkerFiniteUniversal : Prop :=
  ∀ p : ℕ, 0 < p → ∀ parent : WalkerParentSequence, ∀ n : ℕ,
    ∀ (K : Type) [AddCommGroup K] (y : Fin n → K),
      WalkerAssignmentRelations p parent n y →
      ∃! f : (walkerFinitePresentation p parent n).Carrier →+ K,
        ∀ i : Fin n, f ((walkerFinitePresentation p parent n).generator i) = y i

end LogicLineages.ModelsAlgebra.PGroups.Targets
