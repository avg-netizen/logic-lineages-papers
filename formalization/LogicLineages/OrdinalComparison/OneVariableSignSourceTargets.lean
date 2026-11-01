module
public import LogicLineages.OrdinalComparison.OneVariableComparisonDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-- ENTIRE original paper07 thm:sign on its literal two-sort source language.
The encoded signs0,1,2 mean negative,zero,positive. A real total Computable
numeric function must produce the sign AND a positive common genuine-domain
tail for every valid source pair. No supplied comparison, termination,
separation certificate, finite-signature or algorithm interface is a premise. -/
def FullActualOneVariableEventualSigns : Prop :=
  ∃ decision : Nat → Nat → Nat × Nat, Computable₂ decision ∧
    ∀ E F : OneVariableComparisonExpr, oneVariableComparisonValid E → oneVariableComparisonValid F →
      let result := decision (oneVariableComparisonEncode E) (oneVariableComparisonEncode F)
      result.1≤2 ∧ 1≤result.2 ∧ ∀ x : Nat, result.2≤x →
        oneVariableComparisonDomainAt E x ∧ oneVariableComparisonDomainAt F x ∧
        (result.1=0 ↔ actualOneVariableComparisonValue E x<actualOneVariableComparisonValue F x) ∧
        (result.1=1 ↔ actualOneVariableComparisonValue E x=actualOneVariableComparisonValue F x) ∧
        (result.1=2 ↔ actualOneVariableComparisonValue F x<actualOneVariableComparisonValue E x)

end LogicLineages.OrdinalComparison.Targets
