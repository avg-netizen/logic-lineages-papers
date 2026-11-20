module

public import LogicLineages.PersistentMarking.NumberedWindowSyntaxAlgorithm
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowSyntaxProgramTargets
open LogicLineages.ComputabilityKnowledge NumberedWindowSyntaxAlgorithm List.Vector

def BooleanProgram (b : Nat → Bool) : Prop := ∃ p : GorbowPRProgram.Program 1, ∀ n,
  GorbowPRProgram.evaluate p (n ::ᵥ List.Vector.nil) = (b n).toNat

def NominalHeadProgram : Prop := BooleanProgram headBit
def RawTermProgram : Prop := BooleanProgram (fun n => (syntaxBits n).1)
def RawArgumentProgram : Prop := BooleanProgram (fun n => (syntaxBits n).2)
end LogicLineages.PersistentMarking.NumberedWindowSyntaxProgramTargets
