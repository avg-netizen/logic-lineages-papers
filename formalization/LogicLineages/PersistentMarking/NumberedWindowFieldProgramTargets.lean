module

public import LogicLineages.PersistentMarking.NumberedWindowFieldAlgorithm
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowFieldProgramTargets
open LogicLineages.ComputabilityKnowledge List.Vector NumberedWindowFieldAlgorithm

def OrderedFieldPrograms : Prop :=
  (∃ p : GorbowPRProgram.Program 1, ∀ xs,
    GorbowPRProgram.evaluate p (Encodable.encode xs ::ᵥ List.Vector.nil) = pack xs) ∧
  (∃ p : GorbowPRProgram.Program 1, ∀ n,
    GorbowPRProgram.evaluate p (n ::ᵥ List.Vector.nil) = Encodable.encode (unpack n))

def TaggedNodePrograms : Prop :=
  (∃ p : GorbowPRProgram.Program 2, ∀ tag xs,
    GorbowPRProgram.evaluate p (tag ::ᵥ Encodable.encode xs ::ᵥ List.Vector.nil) = packNode tag xs) ∧
  (∃ p : GorbowPRProgram.Program 1, ∀ n,
    GorbowPRProgram.evaluate p (n ::ᵥ List.Vector.nil) = Encodable.encode (unpackNode n))

end LogicLineages.PersistentMarking.NumberedWindowFieldProgramTargets
