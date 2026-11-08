module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalNumericIteration
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The zero count returns the arbitrary original symbolic initial state. -/
def ActualOriginalNumericIterationZero : Prop :=
  ∀ (body : Positive (Fin 1)) (transition : Program 1) (α : Type)
    (out initial : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    ((repeatGraph transition out OrdinaryArithmetic.zeroTerm initial).iff
      (equal out initial)))

/-- A successor count can apply the actual transition to the initial state
first. The premise is its internal graph, not standard-model evaluation. -/
def ActualOriginalNumericIterationFrontSuccessor : Prop :=
  ∀ (body : Positive (Fin 1)) (transition : Program 1) (α : Type)
    (out count initial next : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    ((programGraph transition next (Fin.cons initial Fin.elim0)).imp
      ((repeatGraph transition out (OrdinaryArithmetic.succTerm count) initial).iff
        (repeatGraph transition out count next))))

/-- The first count is performed from the initial state, then the second
from its actual intermediate output. Addition is the original arithmetic
term, not an external sum or a graph of a substituted counting program. -/
def ActualOriginalNumericIterationAdditionFusion : Prop :=
  ∀ (body : Positive (Fin 1)) (transition : Program 1) (α : Type)
    (out first second initial intermediate : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    ((repeatGraph transition intermediate first initial).imp
      ((repeatGraph transition out (OrdinaryArithmetic.addTerm first second) initial).iff
        (repeatGraph transition out second intermediate))))

/-- An actual internal fixed-point graph gives full-output stability at
EVERY arbitrary symbolic count, not merely acceptance at output one. -/
def ActualOriginalNumericIterationFixedPoint : Prop :=
  ∀ (body : Positive (Fin 1)) (transition : Program 1) (α : Type)
    (out count fixed : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    ((programGraph transition fixed (Fin.cons fixed Fin.elim0)).imp
      ((repeatGraph transition out count fixed).iff (equal out fixed))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationTargets
