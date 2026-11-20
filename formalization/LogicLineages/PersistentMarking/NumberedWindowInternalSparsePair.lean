module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePair
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalArithmeticPrograms

/-- Actual sparse source polynomial, not the older max-square Nat.pair. -/
def squaredSum : Program 2 := .composition multiplication ![addition,addition]

def pair : Program 2 := .composition addition ![squaredSum,.projection 0]

/-- Original ordered field cons: one plus pairing the head and raw tail. -/
def fieldCons : Program 2 := .composition .succ (fun _ : Fin 1 => pair)

def pairTerm {α : Type} (x y : OrdinaryArithmetic.Term α) : OrdinaryArithmetic.Term α :=
  let s := OrdinaryArithmetic.addTerm x y
  OrdinaryArithmetic.addTerm (OrdinaryArithmetic.mulTerm s s) x

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePair
