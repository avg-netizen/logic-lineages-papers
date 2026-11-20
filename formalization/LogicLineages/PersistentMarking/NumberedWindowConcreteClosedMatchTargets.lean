module
public import LogicLineages.PersistentMarking.NumberedWindowClosedMatchTargets
public import LogicLineages.PersistentMarking.NumberedWindowConcreteGuardedGraphTargets
@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowConcreteClosedMatchTargets
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowNumericalMatching NumberedWindowClosedMatchTargets NumberedWindowPresentationCheckers
open NumberedWindowFormulaCalibrationTargets NumberedWindowGuardedGraphTargets NumberedWindowFunctionalGraphTargets
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalAccessibilityTargets (Rules)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowAddressApplication (graph)
def ConcreteClosedMatching : Prop :=
  ∀ (xs : Entries) (s : Settings),
    Matching (NumberedWindowConcreteCheckers.positive xs s) (graph s) →
    ∃ (i j : Program 1) (r d p : Program 3), Evaluates (checks xs s) i j r d ∧
      Interprets (checks xs s) (data i j r d) ∧ Rules (data i j r d) ∧
      (∀ f u v, evaluate p (f ::ᵥ u ::ᵥ v ::ᵥ nil) = (graph s f u v).toNat) ∧
      UniqueResult p ∧ InputGuards i j r d p ∧ ∀ c, ClosedMatch r p (sourceBody (data i j r d) c)
end LogicLineages.PersistentMarking.NumberedWindowConcreteClosedMatchTargets
