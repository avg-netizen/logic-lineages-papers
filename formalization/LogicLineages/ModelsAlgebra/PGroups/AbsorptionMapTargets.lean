module
public import LogicLineages.ModelsAlgebra.PGroups.AbsorptionMapDefinitions
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Logic.Encodable.Basic
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary

def groupAbsorptionMapInjective : Prop :=
  ∀ (A C T : Type) [AddCommGroup A] [AddCommGroup C] [AddCommGroup T] (M : ℕ)
    (j : T →+ (ℕ →₀ C)), Function.Injective j → Function.Injective (absorptionMap A C T M j)

def groupAbsorptionMapFixes : Prop :=
  ∀ (A C T : Type) [AddCommGroup A] [AddCommGroup C] [AddCommGroup T] (M : ℕ)
    (j : T →+ (ℕ →₀ C)) (x : A × (ℕ →₀ C)),
    (∀ n ∈ x.2.support, n < M) → absorptionMap A C T M j (x,0) = x

def groupBoundedAbsorptionTupleFixing : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (A T : Type) [AddCommGroup A] [AddCommGroup T] [Countable T] (k : ℕ),
    (∀ t : T, p^k • t = 0) → ∀ (m : ℕ) (a : Fin m → A × (ℕ →₀ ZMod (p^k))),
      ∃ f : ((A × (ℕ →₀ ZMod (p^k))) × T) →+ (A × (ℕ →₀ ZMod (p^k))),
        Function.Injective f ∧ ∀ j, f (a j,0) = a j

end LogicLineages.ModelsAlgebra.PGroups.Targets
