module

public import LogicLineages.ModelsAlgebra.PGroups.CyclicRootDefinitions
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Nat.Prime.Defs

@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary

def groupCyclicRootEvaluation : Prop :=
  ∀ (n : ℕ) (G : Type) [AddCommGroup G] (y : G) (hy : n • y = 0) (a : ℤ),
    cyclicRootHom n G y hy (a : ZMod n) = a • y

def groupCyclicRootGenerator : Prop :=
  ∀ (n : ℕ) (G : Type) [AddCommGroup G] (y : G) (hy : n • y = 0),
    cyclicRootHom n G y hy 1 = y

def groupCyclicRootOrder : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] (j : ℕ) (y : G),
    p ^ (j + 1) • y = 0 → p ^ j • y ≠ 0 → addOrderOf y = p ^ (j + 1)

def groupCyclicRootInjective : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] (j : ℕ) (y : G)
    (hy : p ^ (j + 1) • y = 0), p ^ j • y ≠ 0 →
    Function.Injective (cyclicRootHom (p ^ (j + 1)) G y hy)

end LogicLineages.ModelsAlgebra.PGroups.Targets
