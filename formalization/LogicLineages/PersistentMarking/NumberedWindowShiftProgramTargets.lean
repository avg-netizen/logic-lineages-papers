module

public import LogicLineages.PersistentMarking.NumberedWindowShiftAlgorithm
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowShiftProgramTargets
open LogicLineages.ComputabilityKnowledge NumberedWindowShiftAlgorithm List.Vector

def ShiftProgram : Prop := ∃ p : GorbowPRProgram.Program 3, ∀ amount cutoff n,
  GorbowPRProgram.evaluate p (amount ::ᵥ cutoff ::ᵥ n ::ᵥ List.Vector.nil) =
    Encodable.encode (output amount cutoff n)

end LogicLineages.PersistentMarking.NumberedWindowShiftProgramTargets
