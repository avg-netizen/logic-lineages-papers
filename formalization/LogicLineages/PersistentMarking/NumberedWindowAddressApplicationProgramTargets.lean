module

public import LogicLineages.PersistentMarking.NumberedWindowAddressApplication
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowAddressApplicationProgramTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowAddressApplication NumberedWindowScalarAlgorithm

def ApplicationPrograms : Prop :=
  ∀ s : Settings,
    (∃ p : Program 2, ∀ q u,
      evaluate p (q ::ᵥ u ::ᵥ nil) = Encodable.encode (application s q u)) ∧
    (∃ p : Program 3, ∀ q u v,
      evaluate p (q ::ᵥ u ::ᵥ v ::ᵥ nil) = (graph s q u v).toNat)

end LogicLineages.PersistentMarking.NumberedWindowAddressApplicationProgramTargets
