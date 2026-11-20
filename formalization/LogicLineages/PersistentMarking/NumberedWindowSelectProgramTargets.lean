module

public import LogicLineages.PersistentMarking.NumberedWindowSelectAlgorithm
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowSelectProgramTargets
open LogicLineages.ComputabilityKnowledge NumberedWindowSelectAlgorithm List.Vector

abbrev Parameters := Bool × Nat × List Nat

def SelectProgram : Prop := ∃ p : GorbowPRProgram.Program 3, ∀ (params : Parameters) q r,
  GorbowPRProgram.evaluate p (Encodable.encode params ::ᵥ q ::ᵥ r ::ᵥ List.Vector.nil) =
    (select params.1 params.2.1 params.2.2 q r).toNat

end LogicLineages.PersistentMarking.NumberedWindowSelectProgramTargets
