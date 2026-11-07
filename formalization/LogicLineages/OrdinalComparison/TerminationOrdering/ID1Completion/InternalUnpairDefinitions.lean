module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpair
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The square of the literal original square-root program. -/
def rootSquare : Program 1 := .composition InternalArithmeticPrograms.multiplication
  (Fin.cons InternalSquareRoot.root (Fin.cons InternalSquareRoot.root Fin.elim0))

/-- Original subtraction inputs are [subtrahend,minuend]: n - sqrt(n)^2. -/
def residual : Program 1 := .composition InternalEqualityTest.subtract
  (Fin.cons rootSquare (Fin.cons (.projection (0 : Fin 1)) Fin.elim0))

def residualBelowRoot : Program 1 := .composition InternalLessThan.ltTest
  (Fin.cons residual (Fin.cons InternalSquareRoot.root Fin.elim0))

/-- The literal second subtraction in Nat.unpair: (n - sqrt(n)^2) - sqrt(n). -/
def residualMinusRoot : Program 1 := .composition InternalEqualityTest.subtract
  (Fin.cons InternalSquareRoot.root (Fin.cons residual Fin.elim0))

/-- The first coordinate of the pinned Mathlib Nat.unpair, as an original AST. -/
def left : Program 1 := InternalAcceptance.branch residualBelowRoot InternalSquareRoot.root residual

/-- The second coordinate of the pinned Mathlib Nat.unpair, as an original AST. -/
def right : Program 1 := InternalAcceptance.branch residualBelowRoot residualMinusRoot InternalSquareRoot.root

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpair
