module
public import LogicLineages.ModelsAlgebra.PGroups.TransfiniteTailUlmTargets
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Data.Nat.Prime.Defs
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
universe v

def groupQuotientNextBlockUlmInequality : Prop :=
  ∀ (G : Type) [AddCommGroup G] (p : ℕ) [Fact p.Prime] (δ : Ordinal.{v}) (K T : AddSubgroup G),
    (transfiniteFiltration p δ : AddSubgroup G) = K ⊔ T → Disjoint K T → ∀ j : ℕ,
    Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p (δ+(j : Ordinal.{v})) : AddSubgroup (G ⧸ T))) ≤
    Module.rank (ZMod p) (UlmLayer p (transfiniteFiltration p (δ+(j : Ordinal.{v})) : AddSubgroup G))

end LogicLineages.ModelsAlgebra.PGroups.Targets
