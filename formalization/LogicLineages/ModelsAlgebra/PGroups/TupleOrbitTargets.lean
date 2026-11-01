module
public import LogicLineages.ModelsAlgebra.PGroups.TupleOrbitDefinitions
public import Mathlib.Data.Nat.Prime.Defs
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
/-- Original-language tuple-orbit formula at the actual source short-length
rank. Neither an orbit predicate in syntax nor a supplied Scott family. -/
def shortStableTupleOrbitDefinable : Prop :=
  ∀ (p:ℕ) [Fact p.Prime] (G:Type) [AddCommGroup G] [Countable G]
    (γ:Ordinal.{0}) [Countable γ.ToType] (α:Ordinal.{0}),
    0<γ → Countable α.ToType →
    (∀x:G,∃k:ℕ,p^k • x=0) → α<Ordinal.omega0*γ → StableAt p G α →
    ∀ (n:ℕ) (a:Fin n→G), ∃ φ:Formula n, Complexity .sigma (2*γ) φ ∧
      ∀b:Fin n→G, φ.Realize b ↔ TupleOrbit a b
end LogicLineages.ModelsAlgebra.PGroups.Targets
