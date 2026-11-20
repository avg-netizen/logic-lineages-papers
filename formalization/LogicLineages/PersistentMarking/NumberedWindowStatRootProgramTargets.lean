module
public import LogicLineages.PersistentMarking.NumberedWindowStatRootAlgorithm
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramDefinitions
@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowStatRootProgramTargets
open NumberedWindowStatRootAlgorithm LogicLineages.ComputabilityKnowledge List.Vector
def StatRootProgram : Prop := ∀ entries heads, ∃ p : GorbowPRProgram.Program 3, ∀ q part r,
  GorbowPRProgram.evaluate p (q ::ᵥ part ::ᵥ r ::ᵥ List.Vector.nil) = (stat entries heads part q r).toNat
end LogicLineages.PersistentMarking.NumberedWindowStatRootProgramTargets
