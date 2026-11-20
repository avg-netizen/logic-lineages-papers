module

public import LogicLineages.PersistentMarking.NumberedWindowLexicalAlgorithm
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowLexicalProgramTargets
open LogicLineages.ComputabilityKnowledge NumberedWindowLexicalAlgorithm List.Vector

def RequirementsProgram : Prop := ∃ p : GorbowPRProgram.Program 1, ∀ n,
  GorbowPRProgram.evaluate p (n ::ᵥ List.Vector.nil) = Encodable.encode (requirements n)

def FiniteTypedProgram : Prop := ∃ p : GorbowPRProgram.Program 3, ∀ ctx ty n,
  GorbowPRProgram.evaluate p (Encodable.encode ctx ::ᵥ ty ::ᵥ n ::ᵥ List.Vector.nil) =
    (if typed ctx ty n then 1 else 0)
end LogicLineages.PersistentMarking.NumberedWindowLexicalProgramTargets
