module
public import LogicLineages.ModelsAlgebra.PGroups.WalkerPresentedDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

def walkerPresentedRelations : Prop :=
  ∀ (V : Type) (p : ℕ) (parent : V → Option V) (v : V),
    p • walkerPresentedGenerator p parent v =
      (parent v).elim 0 (walkerPresentedGenerator p parent)

def walkerPresentedUniversal : Prop :=
  ∀ (V : Type) (p : ℕ) (parent : V → Option V)
    (K : Type) [AddCommGroup K] (y : V → K),
    (∀ v, p • y v = (parent v).elim 0 y) →
      ∃! f : WalkerPresentedGroup p parent →+ K,
        ∀ v, f (walkerPresentedGenerator p parent v) = y v

def walkerPresentedHomExt : Prop :=
  ∀ (V : Type) (p : ℕ) (parent : V → Option V)
    (K : Type) [AddCommGroup K] (f g : WalkerPresentedGroup p parent →+ K),
    (∀ v, f (walkerPresentedGenerator p parent v) = g (walkerPresentedGenerator p parent v)) → f = g

end LogicLineages.ModelsAlgebra.PGroups.Targets
