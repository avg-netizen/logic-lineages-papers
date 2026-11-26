module

public import LogicLineages.PersistentMarking.NumberedWindowCoverBoundsAlgorithm
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowCoverBoundsProgramTargets
open LogicLineages.ComputabilityKnowledge NumberedWindowCoverBoundsAlgorithm List.Vector
def MeasureProgram : Prop := ∃ p : GorbowPRProgram.Program 1, ∀ n,
  GorbowPRProgram.evaluate p (n ::ᵥ List.Vector.nil) = Encodable.encode (bounds n)
def SelectedCoverProgram : Prop := ∃ p : GorbowPRProgram.Program 3, ∀ H K n,
  GorbowPRProgram.evaluate p (Encodable.encode H ::ᵥ Encodable.encode K ::ᵥ n ::ᵥ List.Vector.nil) =
    Encodable.encode (cover H K n)
end LogicLineages.PersistentMarking.NumberedWindowCoverBoundsProgramTargets
