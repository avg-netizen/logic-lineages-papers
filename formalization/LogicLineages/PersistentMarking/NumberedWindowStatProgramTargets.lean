module

public import LogicLineages.PersistentMarking.NumberedWindowStatAlgorithm
public import LogicLineages.PersistentMarking.NumberedWindowDirectProgramTargets
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowStatProgramTargets
open LogicLineages.ComputabilityKnowledge NumberedWindowStatAlgorithm List.Vector

def StatPrograms : Prop :=
  (∃ p : GorbowPRProgram.Program 2, ∀ q r,
    GorbowPRProgram.evaluate p (q ::ᵥ r ::ᵥ List.Vector.nil) = (if mark q r then 1 else 0)) ∧
  (∃ p : GorbowPRProgram.Program 3, ∀ q w r,
    GorbowPRProgram.evaluate p (q ::ᵥ w ::ᵥ r ::ᵥ List.Vector.nil) =
      (if replacement q w r then 1 else 0))

end LogicLineages.PersistentMarking.NumberedWindowStatProgramTargets
