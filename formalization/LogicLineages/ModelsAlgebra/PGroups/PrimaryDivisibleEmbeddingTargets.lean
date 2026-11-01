module
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleExtensionDefinitions
public import Mathlib.Logic.Encodable.Basic
public import Mathlib.Data.Nat.Prime.Defs
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
/-- Actual countable primary groups embed into an actual countable
divisible primary group. No injective-hull or embedding oracle is assumed. -/
def countablePrimaryDivisibleEmbedding : Prop :=
  ∀ (p:ℕ) [Fact p.Prime] (T:Type) [AddCommGroup T] [Countable T],
    (∀x:T,∃k:ℕ,p^k • x=0) →
    ∃ (E:Type) (inst:AddCommGroup E),letI:=inst;Countable E ∧
      (∀x:E,∃k:ℕ,p^k • x=0) ∧ GroupDivisible E ∧ ∃i:T→+E,Function.Injective i
end LogicLineages.ModelsAlgebra.PGroups.Targets
