module
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleSplittingDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
/-- Literal divisibility of the target group, not a hom-extension interface. -/
def GroupDivisible (D : Type) [AddCommGroup D] : Prop :=
  ∀ n : ℕ, n ≠ 0 → ∀ x : D, ∃ y : D, n • y = x
end LogicLineages.ModelsAlgebra.PGroups
