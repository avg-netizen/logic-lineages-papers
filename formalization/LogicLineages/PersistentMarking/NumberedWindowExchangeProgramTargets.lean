module

public import LogicLineages.PersistentMarking.NumberedWindowExchangeAlgorithm
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowExchangeProgramTargets
open LogicLineages.ComputabilityKnowledge NumberedWindowExchangeAlgorithm List.Vector
def ContextualExchangeProgram : Prop := ∃ p : GorbowPRProgram.Program 3, ∀ hp a b,
  GorbowPRProgram.evaluate p (Encodable.encode hp ::ᵥ a ::ᵥ b ::ᵥ List.Vector.nil) =
    Encodable.encode (bits hp a b)
end LogicLineages.PersistentMarking.NumberedWindowExchangeProgramTargets
