module

public import LogicLineages.PersistentMarking.NumberedWindowNeutralApplicationAddress
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowNeutralApplicationAddressProgramTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowNeutralApplicationAddress
open NumberedWindowScalarAlgorithm (Settings)

def NeutralFunctionWitnessProgram : Prop :=
  ∀ s : Settings, ∃ p : Program 2, ∀ source certificate,
    evaluate p (source ::ᵥ certificate ::ᵥ nil) =
      Encodable.encode (functionWitness s source certificate)

end LogicLineages.PersistentMarking.NumberedWindowNeutralApplicationAddressProgramTargets
