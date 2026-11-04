module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityFormulaProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceFiniteComputabilityFormula
open FirstOrder Language Source PositiveArithmeticOperators SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative

def typeGuard (tau : Ty) : language.Formula (Fin 3) :=
  arithmeticEmbedding.onFormula ((.var 1 : OrdinaryArithmetic.Term (Fin 3)).equal (numeral (typeNumber tau)))

def windowFormula (formulas : Ty → language.Formula (Fin 2)) : List Ty → language.Formula (Fin 3)
  | [] => ⊥
  | tau :: rest => (typeGuard tau ⊓ (formulas tau).relabel ![0,2]) ⊔ windowFormula formulas rest
end LogicLineages.OrdinalComparison.TerminationOrdering.SourceFiniteComputabilityFormula
