module

public import LogicLineages.PersistentMarking.NumberedWindowRawApplicationLift
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowRawApplicationLiftProgramTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowRawApplicationLift

def RawApplicationLiftProgram : Prop :=
  ∃ p : Program 6, ∀ domain result argument source certificate target,
    evaluate p (domain ::ᵥ result ::ᵥ argument ::ᵥ source ::ᵥ certificate ::ᵥ target ::ᵥ nil) =
      Encodable.encode (lift domain result argument source certificate target)

end LogicLineages.PersistentMarking.NumberedWindowRawApplicationLiftProgramTargets
