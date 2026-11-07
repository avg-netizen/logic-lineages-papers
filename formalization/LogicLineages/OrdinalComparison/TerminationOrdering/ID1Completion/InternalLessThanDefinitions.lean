module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThan
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def constantOne (n : Nat) : Program n :=
  .composition .succ (fun _ : Fin 1 => InternalAcceptance.constantZero n)

/-- The original subtraction AST has inputs [x,y] and output y-x.
Its zero branch rejects; its successor branch accepts with exactly one. -/
def ltTest : Program 2 := InternalAcceptance.branch InternalEqualityTest.subtract
  (InternalAcceptance.constantZero 2) (constantOne 2)

def strictLess {α : Type} (x y : OrdinaryArithmetic.Term α) : Formula α :=
  arithmeticEmbedding.onFormula (OrdinaryArithmetic.lessFormula x y)

def lessThanSpec {α : Type} (out x y : OrdinaryArithmetic.Term α) : Formula α :=
  (strictLess x y ⊓ equal out (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm)) ⊔
  ((strictLess x y).not ⊓ equal out OrdinaryArithmetic.zeroTerm)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThan
