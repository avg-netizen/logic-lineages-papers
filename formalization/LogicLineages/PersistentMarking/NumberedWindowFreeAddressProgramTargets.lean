module

public import LogicLineages.PersistentMarking.NumberedWindowFreeAddress
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowFreeAddressProgramTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowFreeAddress

def FreeAddressPrograms : Prop :=
  (∃ p : Program 3, ∀ context type name,
    evaluate p (Encodable.encode context ::ᵥ type ::ᵥ name ::ᵥ nil) = freeAddress context type name) ∧
  (∃ p : Program 1, ∀ term,
    evaluate p (term ::ᵥ nil) = freshName term)

end LogicLineages.PersistentMarking.NumberedWindowFreeAddressProgramTargets
