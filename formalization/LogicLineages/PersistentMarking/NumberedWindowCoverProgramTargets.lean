module

public import LogicLineages.PersistentMarking.NumberedWindowCoverAlgorithm
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowCoverProgramTargets
open LogicLineages.ComputabilityKnowledge NumberedWindowCoverAlgorithm List.Vector

def CoverGrammarProgram : Prop := ∃ p : GorbowPRProgram.Program 4, ∀ H K num depth,
  GorbowPRProgram.evaluate p (Encodable.encode H ::ᵥ Encodable.encode K ::ᵥ num ::ᵥ depth ::ᵥ List.Vector.nil) =
    Encodable.encode (grammar H K num depth)

end LogicLineages.PersistentMarking.NumberedWindowCoverProgramTargets
