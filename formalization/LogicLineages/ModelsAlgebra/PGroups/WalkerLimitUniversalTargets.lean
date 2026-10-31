module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerLimitUniversalDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

def walkerLimitUniversal : Prop :=
  ∀ p : ℕ, 0 < p → ∀ parent : WalkerParentSequence,
    ∀ (K : Type) [AddCommGroup K] (y : ℕ → K),
      WalkerSequentialAssignment p parent y →
      ∃! f : WalkerSequentialGroup p parent →+ K,
        ∀ i, f (walkerSequentialGenerator p parent i) = y i

def walkerLimitHomExt : Prop :=
  ∀ p : ℕ, 0 < p → ∀ parent : WalkerParentSequence,
    ∀ (K : Type) [AddCommGroup K] (f g : WalkerSequentialGroup p parent →+ K),
      (∀ i, f (walkerSequentialGenerator p parent i) = g (walkerSequentialGenerator p parent i)) → f = g

end LogicLineages.ModelsAlgebra.PGroups.Targets
