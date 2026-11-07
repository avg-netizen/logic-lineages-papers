module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTest
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open LogicLineages.ComputabilityKnowledge LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- A new literal original Program AST: the step returns the previous counter. -/
def predecessor : Program 1 := .recursion .zero (.projection (0 : Fin 2))

/-- The recursion step decrements the previous result, ignoring its counter
and the unchanged minuend parameter. -/
def subtractStep : Program 3 :=
  .composition predecessor (fun _ : Fin 1 => .projection (1 : Fin 3))

/-- Inputs are [counter, minuend]; evaluation is minuend - counter. -/
def subtract : Program 2 := .recursion (.projection (0 : Fin 1)) subtractStep

def reverseSubtract : Program 2 :=
  .composition subtract (Fin.cons (.projection (1 : Fin 2))
    (Fin.cons (.projection (0 : Fin 2)) Fin.elim0))

def reverseZeroTest : Program 2 :=
  .composition GorbowPRInternalControl.zeroTest (fun _ : Fin 1 => reverseSubtract)

def zeroBinary : Program 2 := .composition .zero Fin.elim0

/-- The existing conditional selects its second input precisely when its
first input is zero. Thus both truncated differences must be zero. -/
def equalityTest : Program 2 :=
  .composition GorbowPRInternalControl.conditional
    (Fin.cons subtract (Fin.cons reverseZeroTest (Fin.cons zeroBinary Fin.elim0)))

/-- Exact predecessor relation, including the exceptional zero case. -/
def predecessorSpec {α : Type} (out input : OrdinaryArithmetic.Term α) : Formula α :=
  (equal input OrdinaryArithmetic.zeroTerm ⊓ equal out OrdinaryArithmetic.zeroTerm) ⊔
    equal input (OrdinaryArithmetic.succTerm out)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTest
