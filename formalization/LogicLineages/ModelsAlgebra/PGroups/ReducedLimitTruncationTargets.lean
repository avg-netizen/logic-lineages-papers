module
public import LogicLineages.ModelsAlgebra.PGroups.PrescribedTailDefinitions
public import Mathlib.Data.Nat.Prime.Defs
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
/-- Quotient by the actual limit cut has exactly that length and actual
infinite socles at every earlier stage; these are proved, not supplied as
an abstract admissibility condition for the later pullback construction. -/
def actualReducedLimitTruncation : Prop :=
  ∀ (p:ℕ) [Fact p.Prime] (G:Type) [AddCommGroup G] [Countable G]
    (δ:Ordinal.{0}),Order.IsSuccLimit δ →
    (∀x:G,∃k:ℕ,p^k • x=0) → IsReducedAddGroup G → StagesNonzeroBelow p G δ →
    let Q:=G⧸(transfiniteFiltration p δ:AddSubgroup G)
    Countable Q ∧ (∀x:Q,∃k:ℕ,p^k • x=0) ∧ IsReducedAddGroup Q ∧
      PGroupExactLength p Q δ ∧ SoclesInfiniteBelow p Q δ
end LogicLineages.ModelsAlgebra.PGroups.Targets
