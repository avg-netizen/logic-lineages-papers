module

public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryDualDefinitions

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.Targets

open GroupInfinitary
universe u v

def groupInfinitaryDualRealization : Prop :=
  ∀ (G : Type u) [AddCommGroup G] (n : ℕ) (φ : Formula n) (a : Fin n → G),
    φ.dual.Realize a ↔ ¬ φ.Realize a

def groupInfinitaryDualComplexity : Prop :=
  ∀ (side : Polarity) (α : Ordinal.{v}) (n : ℕ) (φ : Formula n),
    Complexity side α φ → Complexity side.opposite α φ.dual

end LogicLineages.ModelsAlgebra.PGroups.Targets
