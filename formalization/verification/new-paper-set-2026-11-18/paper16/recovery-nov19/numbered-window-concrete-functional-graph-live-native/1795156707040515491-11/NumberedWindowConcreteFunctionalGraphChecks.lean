module
public import LogicLineages.PersistentMarking.NumberedWindowConcreteFunctionalGraphTargets
import LogicLineages.PersistentMarking.NumberedWindowFunctionalGraphChecks
import LogicLineages.PersistentMarking.NumberedWindowAddressApplicationProgramChecks
public section
namespace LogicLineages.PersistentMarking.NumberedWindowConcreteFunctionalGraphChecks
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowConcreteFunctionalGraphTargets NumberedWindowFunctionalGraphTargets
open NumberedWindowAddressApplication NumberedWindowFunctionalGraphChecks

theorem exact_ConcreteFunctionalApplication : ConcreteFunctionalApplication := by
  intro s
  obtain ⟨a,ha⟩ := (NumberedWindowAddressApplicationProgramChecks.exact_ApplicationPrograms s).1
  obtain ⟨connect,unique⟩ := exact_FunctionalGraph a
  refine ⟨a,graphProgram a,ha,?_,connect,unique⟩
  intro f u v
  rw [exact_Evaluation a f u v,ha]
  unfold graph
  cases h : application s f u with
  | none => simp
  | some w =>
    by_cases hv : v = w
    · subst w
      simp
    · have hfalse : (w == v) = false := by
        cases hb : w == v with
        | false => rfl
        | true => exact False.elim (hv (eq_of_beq hb).symm)
      simp [hv,hfalse]

#print axioms exact_ConcreteFunctionalApplication
end LogicLineages.PersistentMarking.NumberedWindowConcreteFunctionalGraphChecks
