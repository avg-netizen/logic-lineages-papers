module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedExactVariablesLiteralProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedTypedCompilerSemanticProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedExactVariables.Proof

/-- Tautological original-support padding preserves the accepted actual sign
comparison under exactly its original semantic premises and raw valuation. -/
theorem actualSignSemantics : Targets.ActualSignSemantics := by
  intro Γ C E F desired ν hC hE hF hpositive
  exact ((truthAndExactVariables Γ C E F desired).1 ν).trans
    (BalancedTypedCompiler.Proof.actualSignSemantics
      Γ C E F desired ν hC hE hF hpositive)

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedExactVariables.Proof
