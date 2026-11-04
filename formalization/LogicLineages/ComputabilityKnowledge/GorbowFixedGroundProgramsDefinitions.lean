module

public import LogicLineages.ComputabilityKnowledge.GorbowPublishedModelDefinitions
public import LogicLineages.ComputabilityKnowledge.GorbowNamedRegistryInterpretationDefinitions

@[expose] public section
/-! Effectivity of a FIXED finite PR registry and its real total named overlay.
Program ASTs are fixed parameters OUTSIDE each Primrec assertion. There is
no uniform evaluator taking an arbitrary PR AST as a runtime input. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowFixedGroundPrograms
open GorbowPRProgram

def checkedEvaluation {n : Nat} (p : Program n) (args : List Nat) : Option Nat :=
  if h : args.length = n then some (evaluate p ⟨args,h⟩) else none

end LogicLineages.ComputabilityKnowledge.GorbowFixedGroundPrograms
