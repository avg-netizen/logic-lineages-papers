module

public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureCombine
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion

def callOne {n : Nat} (p : Program 1) (q : Program n) : Program n :=
  .composition p (fun _ : Fin 1 => q)

def callTwo {n : Nat} (p : Program 2) (q r : Program n) : Program n :=
  .composition p ![q,r]

def coordinate (p : Program 1) (i : Fin 2) : Program 2 := callOne p (.projection i)

/-- The genuine original less-than test chooses the second bound only when
the first is smaller. The physical tie branch keeps the first. -/
def maximum : Program 2 :=
  InternalAcceptance.branch InternalLessThan.ltTest (.projection 0) (.projection 1)

def predecessorDepth : Program 2 := callTwo InternalArithmeticPrograms.addition
  (coordinate InternalUnpair.left 0) (coordinate InternalUnpair.left 1)

def numeralBound : Program 2 := callTwo maximum
  (coordinate InternalUnpair.right 0) (coordinate InternalUnpair.right 1)

/-- Literal unshifted pair, not sparse cons or an Option wrapper.
The true input tape is the two actual encoded child measure results. -/
def chosenCombine : Program 2 :=
  callTwo InternalPairing.pairing (callOne .succ predecessorDepth) numeralBound

end LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureCombine
