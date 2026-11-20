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
    · simp [hv,Ne.symm hv]

#print axioms exact_ConcreteFunctionalApplication
end LogicLineages.PersistentMarking.NumberedWindowConcreteFunctionalGraphChecks
