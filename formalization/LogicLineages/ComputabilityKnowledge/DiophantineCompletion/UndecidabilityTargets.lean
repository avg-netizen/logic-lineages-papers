module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.UndecidabilityDefinitions
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.Targets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.UndecidabilityTargets
open Undecidability

def NatHaltingRE : Prop := REPred natHaltsZero

def NatHaltingUndecidable : Prop := ¬ ComputablePred natHaltsZero

-- The final comparator is the unchanged Targets.EncodedPolynomialUndecidable.
-- Neither the RE reduction nor any undecidability statement is a premise.
end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.UndecidabilityTargets
