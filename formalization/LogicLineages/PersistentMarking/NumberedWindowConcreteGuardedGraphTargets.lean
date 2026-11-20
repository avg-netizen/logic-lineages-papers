module
public import LogicLineages.PersistentMarking.NumberedWindowGuardedGraphTargets
public import LogicLineages.PersistentMarking.NumberedWindowConcreteFunctionalGraphTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalAccessibilityTargets
@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowConcreteGuardedGraphTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowFunctionalGraphTargets NumberedWindowGuardedGraphTargets
open NumberedWindowFormulaCalibrationTargets NumberedWindowPresentationCheckers
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalAccessibilityTargets (Rules)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowAddressApplication (graph)

def ConcreteGuardedApplication : Prop :=
  ∀ (xs : Entries) (s : Settings), ∃ (i j : Program 1) (r d p : Program 3),
    Evaluates (checks xs s) i j r d ∧ Interprets (checks xs s) (data i j r d) ∧ Rules (data i j r d) ∧
    (∀ f u v, evaluate p (f ::ᵥ u ::ᵥ v ::ᵥ nil) = (graph s f u v).toNat) ∧
    UniqueResult p ∧ InputGuards i j r d p
end LogicLineages.PersistentMarking.NumberedWindowConcreteGuardedGraphTargets
