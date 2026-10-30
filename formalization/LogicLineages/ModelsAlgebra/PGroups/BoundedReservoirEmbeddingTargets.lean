module
public import LogicLineages.ModelsAlgebra.PGroups.PowerCyclicDefinitions
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Nat.Prime.Defs
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets

/-- Actual countable bounded groups embed in a countable reservoir of maximal
cyclic factors, including the honest k=0 trivial case. -/
def groupBoundedReservoirEmbedding : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (T : Type) [AddCommGroup T] [Countable T] (k : ℕ),
    (∀ t : T, p^k • t = 0) →
      ∃ f : T →+ (ℕ →₀ ZMod (p^k)), Function.Injective f

end LogicLineages.ModelsAlgebra.PGroups.Targets
