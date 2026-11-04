module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceFiniteComputabilityFormulaProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceEnvironmentComputabilityFormula
open Source PositiveArithmeticOperators
/-- Left singleton is the target Context code; right coordinates follow Gamma literally. -/
def environmentFormula (formulas : Ty → language.Formula (Fin 2)) :
    (Gamma : List Ty) → language.Formula (Fin 1 ⊕ Fin Gamma.length)
  | [] => ⊤
  | tau :: rest => (formulas tau).relabel ![Sum.inl 0,Sum.inr 0] ⊓
      (environmentFormula formulas rest).relabel (Sum.map id Fin.succ)
end LogicLineages.OrdinalComparison.TerminationOrdering.SourceEnvironmentComputabilityFormula
