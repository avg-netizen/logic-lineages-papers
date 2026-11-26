module
public import LogicLineages.PersistentMarking.NumberedWindowTypedProbe
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramDefinitions
@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowTypedProbeProgramTargets
open NumberedWindowTypedProbe NumberedWindowScalarAlgorithm
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
def TypedProbePrograms : Prop := ∀ s : Settings,
  (∃ p : Program 2, ∀ t n, evaluate p (t ::ᵥ n ::ᵥ nil) = (typed s t n).toNat) ∧
  (∃ p : Program 1, ∀ n, evaluate p (n ::ᵥ nil) = Encodable.encode (probe s n))
end LogicLineages.PersistentMarking.NumberedWindowTypedProbeProgramTargets
