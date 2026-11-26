module
public import LogicLineages.PersistentMarking.NumberedWindowFormulaCalibrationTargets
public import LogicLineages.PersistentMarking.NumberedWindowPresentationCheckers

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowConcreteFormulaTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowPresentationCheckers NumberedWindowFormulaCalibrationTargets
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowCopyAlgorithm (Entries) NumberedWindowScalarAlgorithm (Settings)

/-- A single choice of the original four programs provides the actual uniform
formula data for every outer context and predicate. -/
def ConcretePresentation : Prop := ∀ (xs : Entries) (s : Settings),
  ∃ (i j : Program 1) (r d : Program 3),
    Evaluates (checks xs s) i j r d ∧ Interprets (checks xs s) (data i j r d)
end LogicLineages.PersistentMarking.NumberedWindowConcreteFormulaTargets
