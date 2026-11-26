module

public import LogicLineages.PersistentMarking.NumberedWindowScalarAlgorithm
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowScalarProgramTargets
open LogicLineages.ComputabilityKnowledge NumberedWindowScalarAlgorithm List.Vector

def FixedLeastProgram : Prop := ∀ s : Settings, ∃ p : GorbowPRProgram.Program 3, ∀ ctx ty seed,
  GorbowPRProgram.evaluate p (Encodable.encode ctx ::ᵥ ty ::ᵥ seed ::ᵥ List.Vector.nil) =
    Encodable.encode (least s ctx ty seed)

def FixedScalarProgram : Prop := ∀ s : Settings, ∃ p : GorbowPRProgram.Program 1, ∀ n,
  GorbowPRProgram.evaluate p (n ::ᵥ List.Vector.nil) = if scalar s n then 1 else 0

end LogicLineages.PersistentMarking.NumberedWindowScalarProgramTargets
