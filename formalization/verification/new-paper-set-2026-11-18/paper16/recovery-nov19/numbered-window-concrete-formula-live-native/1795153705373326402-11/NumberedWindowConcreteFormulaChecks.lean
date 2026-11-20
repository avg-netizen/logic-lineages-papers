module
public import LogicLineages.PersistentMarking.NumberedWindowConcreteFormulaTargets
import LogicLineages.PersistentMarking.NumberedWindowConcreteCheckersProgramChecks
import LogicLineages.PersistentMarking.NumberedWindowFormulaCalibrationChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowConcreteFormulaChecks
open NumberedWindowConcreteFormulaTargets NumberedWindowFormulaCalibrationTargets
open NumberedWindowPresentationCheckers

theorem exact_ConcretePresentation : ConcretePresentation := by
  intro xs s
  obtain ⟨⟨i,hi⟩, ⟨j,hj⟩, ⟨r,hr⟩, ⟨d,hd⟩⟩ :=
    NumberedWindowConcreteCheckersProgramChecks.exact_AllFourProgramWitnesses xs s
  have h : Evaluates (checks xs s) i j r d := ⟨hi,hj,hr,hd⟩
  exact ⟨i,j,r,d,h,NumberedWindowFormulaCalibrationChecks.exact_InterpretsEvaluatingPrograms _ _ _ _ _ h⟩

#print axioms exact_ConcretePresentation
end LogicLineages.PersistentMarking.NumberedWindowConcreteFormulaChecks
