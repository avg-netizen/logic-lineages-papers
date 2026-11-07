module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumeralEvaluationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumeralEvaluationTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition
open SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- A genuine original-calculus proof tree for each concrete evaluation of
every original Program, including recursion. The free-variable type is
arbitrary; the graph instance itself contains only numeral terms. -/
def ActualOriginalNumeralEvaluation : Prop :=
  ∀ (body : Positive (Fin 1)) (n : Nat) (p : Program n) (v : List.Vector Nat n) (α : Type),
  Nonempty (Derivation body []
    (graph (OrdinaryArithmetic.graphFormula p) (numeral (evaluate p v))
      (fun i => (numeral (v.get i) : OTerm α))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumeralEvaluationTargets
