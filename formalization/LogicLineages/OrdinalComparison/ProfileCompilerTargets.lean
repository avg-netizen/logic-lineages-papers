module
public import LogicLineages.OrdinalComparison.ProfileCompilerDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-! Paper07 lem:reserve (464–495), first binary-tree compiler stage.
No reserve consumption or R/H claim is assumed in these propositions. -/
def ActualFixedLimitProfileMonotone : Prop :=
  ∀ L : Ordinal.{0}, ∀ E : FixedLimitPositiveExpr, fixedLimitProfileBelow L E →
    Monotone (actualFixedLimitProfileEval E)

def ActualProfileBoundCompiler : Prop :=
  ∀ L : Ordinal.{0}, Ordinal.omega0 < L → ∀ E : FixedLimitPositiveExpr,
    fixedLimitProfileBelow L E →
    profileBoundWord E ≠ [] ∧
    (∀ rho ∈ profileBoundWord E, Order.IsSuccLimit rho.1.repr ∧ rho.1.repr < L) ∧
    ∀ x : Nat, fixedLimitProfileThreshold E ≤ x →
      actualFixedLimitProfileEval E x < actualProfileWordValue (profileBoundWord E) x ∧
      x < actualProfileWordValue (profileBoundWord E) x

end LogicLineages.OrdinalComparison.Targets
