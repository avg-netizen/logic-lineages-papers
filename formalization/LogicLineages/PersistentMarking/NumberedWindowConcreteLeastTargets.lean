module
public import LogicLineages.PersistentMarking.NumberedWindowConcreteFormulaTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalLeastTargets
public import LogicLineages.PersistentMarking.NumberedWindowPresentationLeast
@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowConcreteLeastTargets
open LogicLineages.OrdinalComparison.TerminationOrdering ID1Completion.SourcePresentation
open ID1Completion.InternalCalculus PositiveArithmeticOperators
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowPresentationCheckers NumberedWindowFormulaCalibrationTargets
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowPresentationLeast NumberedWindowPresentationClauses

def ConcreteLeastInterpretation : Prop := ∀ (xs : Entries) (s : Settings),
  ∃ (i j : Program 1) (r d : Program 3), Evaluates (checks xs s) i j r d ∧
    ∀ context,
      let src := data i j r d
      let pred := standardLeastPredicate (sourceBody src context)
      (∀ z, pred z ↔ least (checks xs s) z) ∧
        (realize pred (allTermsFormula src context) Empty.elim ↔
          terms (checks xs s) (least (checks xs s)))
end LogicLineages.PersistentMarking.NumberedWindowConcreteLeastTargets
