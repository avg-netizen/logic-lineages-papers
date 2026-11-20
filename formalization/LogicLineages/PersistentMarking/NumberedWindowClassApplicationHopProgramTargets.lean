module

public import LogicLineages.PersistentMarking.NumberedWindowClassApplicationHop
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowClassApplicationHopProgramTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowClassApplicationHop

def ClassHopLiftProgram : Prop :=
  ∀ least : Nat → Option Nat, Primrec least →
    ∃ p : Program 4, ∀ domain result argument code,
      evaluate p (domain ::ᵥ result ::ᵥ argument ::ᵥ code ::ᵥ nil) =
        Encodable.encode (liftHop least domain result argument code)

end LogicLineages.PersistentMarking.NumberedWindowClassApplicationHopProgramTargets
