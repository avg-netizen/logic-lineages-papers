module
public import LogicLineages.PersistentMarking.NumberedWindowSingletonAlgorithm
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramDefinitions
@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowSingletonProgramTargets
open LogicLineages.ComputabilityKnowledge NumberedWindowSingletonAlgorithm List.Vector
def SingletonProgram : Prop := ∃ p : GorbowPRProgram.Program 3, ∀ arg depth n,
  GorbowPRProgram.evaluate p (arg ::ᵥ depth ::ᵥ n ::ᵥ List.Vector.nil) = Encodable.encode (output arg depth n)
end LogicLineages.PersistentMarking.NumberedWindowSingletonProgramTargets
