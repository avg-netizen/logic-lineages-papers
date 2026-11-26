module

public import LogicLineages.PersistentMarking.NumberedWindowMarkRootAlgorithm
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramDefinitions
@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowMarkRootProgramTargets
open LogicLineages.ComputabilityKnowledge NumberedWindowMarkRootAlgorithm List.Vector

def UnaryLabelProgram : Prop := ∃ p : GorbowPRProgram.Program 3, ∀ k q r,
  GorbowPRProgram.evaluate p (k ::ᵥ q ::ᵥ r ::ᵥ List.Vector.nil) = (mark k q r).toNat
def BinaryProgram (f : Nat → Nat → Bool) : Prop := ∃ p : GorbowPRProgram.Program 2, ∀ q r,
  GorbowPRProgram.evaluate p (q ::ᵥ r ::ᵥ List.Vector.nil) = (f q r).toNat

def SimpleRootPrograms : Prop := UnaryLabelProgram ∧ BinaryProgram lower ∧ BinaryProgram bottom
end LogicLineages.PersistentMarking.NumberedWindowMarkRootProgramTargets
