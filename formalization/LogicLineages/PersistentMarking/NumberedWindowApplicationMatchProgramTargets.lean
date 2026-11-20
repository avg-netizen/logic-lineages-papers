module

public import LogicLineages.PersistentMarking.NumberedWindowApplicationMatch
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowApplicationMatchProgramTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowApplicationMatch
open NumberedWindowScalarAlgorithm (Settings)

def ApplicationMatchProgram : Prop :=
  ∀ s : Settings, ∃ p : Program 3, ∀ source argument certificate,
    evaluate p (source ::ᵥ argument ::ᵥ certificate ::ᵥ nil) =
      Encodable.encode (matchingCertificate s source argument certificate)

end LogicLineages.PersistentMarking.NumberedWindowApplicationMatchProgramTargets
