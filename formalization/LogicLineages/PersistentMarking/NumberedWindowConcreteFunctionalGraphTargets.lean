module
public import LogicLineages.PersistentMarking.NumberedWindowFunctionalGraphTargets
public import LogicLineages.PersistentMarking.NumberedWindowAddressApplicationProgramTargets
@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowConcreteFunctionalGraphTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowFunctionalGraphTargets NumberedWindowAddressApplication
open NumberedWindowScalarAlgorithm (Settings)

/-- The same chosen programs support exact evaluation and open-term internal uniqueness. -/
def ConcreteFunctionalApplication : Prop :=
  ∀ s : Settings, ∃ (a : Program 2) (p : Program 3),
    (∀ f u, evaluate a (f ::ᵥ u ::ᵥ nil) = Encodable.encode (application s f u)) ∧
    (∀ f u v, evaluate p (f ::ᵥ u ::ᵥ v ::ᵥ nil) = (graph s f u v).toNat) ∧
    OutputRule a p ∧ UniqueResult p

end LogicLineages.PersistentMarking.NumberedWindowConcreteFunctionalGraphTargets
