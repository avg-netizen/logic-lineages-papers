module
public import LogicLineages.OrdinalComparison.KernelQuadraticSourceComparisonDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelQuadraticSourceComparison.Targets
/-- Explicit comparison of the two formal interpretations, for every t ≥ 4. -/
def ExactUniformComparison : Prop :=
  ∀ t : Nat, 4 ≤ t →
    KernelConcreteCountConvention.companionCount t = displayedCount t ∧
    displayedCount t < KernelConcreteCountConvention.wholeCount t
/-- No eventual equality to the displayed formula under the literal
whole-current-state scheduled interpretation. This is not a rank≥3 claim. -/
def NoLiteralEqualityTail : Prop :=
  (∀ T : Nat, ∃ t : Nat, T ≤ t ∧ 4 ≤ t ∧
    displayedCount t < KernelConcreteCountConvention.wholeCount t) ∧
  ¬ ∃ T : Nat, ∀ t : Nat, T ≤ t →
    KernelConcreteCountConvention.wholeCount t = displayedCount t
end LogicLineages.OrdinalComparison.KernelQuadraticSourceComparison.Targets
