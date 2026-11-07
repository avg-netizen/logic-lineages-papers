module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumeralEvaluation
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition
open SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The literal ordinary arithmetic graph at the actual value of the original
program and the original ordered vector of numeral inputs. No semantic
reflection rule or alternative program syntax occurs in this formula. -/
def evaluatedGraph {n : Nat} {α : Type} (p : Program n) (v : List.Vector Nat n) : Formula α :=
  graph (OrdinaryArithmetic.graphFormula p) (numeral (evaluate p v)) (fun i => numeral (v.get i))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumeralEvaluation
