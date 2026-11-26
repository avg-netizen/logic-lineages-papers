module

public import LogicLineages.PersistentMarking.NumberedWindowClassApplicationPath
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowClassApplicationPathProgramTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowClassApplicationPath

def ClassPathLiftProgram : Prop :=
  ∀ least : Nat → Option Nat, Primrec least →
    ∃ p : Program 5, ∀ domain result argument imageSource certificate,
      evaluate p (domain ::ᵥ result ::ᵥ argument ::ᵥ imageSource ::ᵥ certificate ::ᵥ nil) =
        Encodable.encode (liftPath least domain result argument imageSource certificate)

end LogicLineages.PersistentMarking.NumberedWindowClassApplicationPathProgramTargets
