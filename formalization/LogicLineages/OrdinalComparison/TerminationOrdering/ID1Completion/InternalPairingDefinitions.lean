module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsDefinitions
public import Mathlib.Data.Nat.Pairing
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairing
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram InternalArithmeticPrograms

def squareFirst : Program 2 :=
  .composition multiplication (fun _ : Fin 2 => .projection (0 : Fin 2))

def squareSecond : Program 2 :=
  .composition multiplication (fun _ : Fin 2 => .projection (1 : Fin 2))

def squareFirstPlusFirst : Program 2 :=
  .composition addition (Fin.cons squareFirst
    (Fin.cons (.projection (0 : Fin 2)) Fin.elim0))

/-- Original Nat.pair non-strict branch x*x+x+y. -/
def nonLessBranch : Program 2 :=
  .composition addition (Fin.cons squareFirstPlusFirst
    (Fin.cons (.projection (1 : Fin 2)) Fin.elim0))

/-- Original Nat.pair strict branch y*y+x. -/
def lessBranch : Program 2 :=
  .composition addition (Fin.cons squareSecond
    (Fin.cons (.projection (0 : Fin 2)) Fin.elim0))

/-- Literal Mathlib Nat.pair AST, not the different Gorbow square pairing. -/
def pairing : Program 2 :=
  InternalAcceptance.branch InternalLessThan.ltTest nonLessBranch lessBranch

def pairingSpec {α : Type} (out x y : OrdinaryArithmetic.Term α) : Formula α :=
  (InternalLessThan.strictLess x y ⊓
    equal out (OrdinaryArithmetic.addTerm (OrdinaryArithmetic.mulTerm y y) x)) ⊔
  ((InternalLessThan.strictLess x y).not ⊓
    equal out (OrdinaryArithmetic.addTerm
      (OrdinaryArithmetic.addTerm (OrdinaryArithmetic.mulTerm x x) x) y))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairing
