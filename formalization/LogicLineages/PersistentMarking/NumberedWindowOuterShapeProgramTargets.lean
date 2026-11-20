module

public import LogicLineages.PersistentMarking.NumberedWindowOuterShape
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowOuterShapeProgramTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowOuterShape
open NumberedWindowScalarAlgorithm (Settings)

def OuterShapeProgram : Prop :=
  ∀ s : Settings, ∃ p : Program 1, ∀ n,
    evaluate p (n ::ᵥ nil) = Encodable.encode (outerShape s n)

end LogicLineages.PersistentMarking.NumberedWindowOuterShapeProgramTargets
