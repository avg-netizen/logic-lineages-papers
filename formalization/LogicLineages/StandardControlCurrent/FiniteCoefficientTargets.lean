module
public import LogicLineages.OrdinalComparison.ActualCollapseDefinitions

@[expose] public section
namespace LogicLineages.StandardControlCurrent.FiniteCoefficientTargets
open OrdinalComparison

/-- Full current18 f:cor:finite-coefficient on the independently defined
actual ordinal collapse. All k,n include zero; operations on ordinals are
ordinary omega*k+n, and the control remains literal Phi=F5(n+100). -/
def FiniteCoefficient : Prop :=
  ∀ k n : Nat,
    actualCollapse (Ordinal.omega0 * (k : Ordinal) + (n : Ordinal)) =
      (Phi^[k]) (2 * k + n) + k

end LogicLineages.StandardControlCurrent.FiniteCoefficientTargets
