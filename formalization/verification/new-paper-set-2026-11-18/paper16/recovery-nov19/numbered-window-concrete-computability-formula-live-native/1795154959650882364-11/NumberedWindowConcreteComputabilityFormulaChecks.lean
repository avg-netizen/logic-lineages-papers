module
public import LogicLineages.PersistentMarking.NumberedWindowConcreteComputabilityFormulaTargets
import LogicLineages.PersistentMarking.NumberedWindowComputabilityFormulaChecks
import LogicLineages.PersistentMarking.NumberedWindowAddressApplicationProgramChecks
public section
namespace LogicLineages.PersistentMarking.NumberedWindowConcreteComputabilityFormulaChecks
open NumberedWindowConcreteComputabilityFormulaTargets NumberedWindowComputabilityFormulaTargets
open NumberedWindowAddressApplicationProgramChecks NumberedWindowAddressApplication

theorem exact_ConcreteTypeComputabilityFormula : ConcreteTypeComputabilityFormula := by
  intro s
  obtain ⟨p,hp⟩ := (exact_ApplicationPrograms s).2
  have eqGraph : graphHolds p = fun x u v => graph s x u v = true := by
    funext x u v
    apply propext
    unfold graphHolds
    rw [hp]
    cases graph s x u v <;> decide
  refine ⟨p,hp,?_⟩
  intro τ α q P env
  rw [NumberedWindowComputabilityFormulaChecks.exact_TypeFormulaReading, eqGraph]

#print axioms exact_ConcreteTypeComputabilityFormula
end LogicLineages.PersistentMarking.NumberedWindowConcreteComputabilityFormulaChecks
