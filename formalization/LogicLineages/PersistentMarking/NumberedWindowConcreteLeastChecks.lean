module
public import LogicLineages.PersistentMarking.NumberedWindowConcreteLeastTargets
import LogicLineages.PersistentMarking.NumberedWindowConcreteFormulaChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalLeastChecks
public section
namespace LogicLineages.PersistentMarking.NumberedWindowConcreteLeastChecks
open NumberedWindowConcreteLeastTargets NumberedWindowConcreteFormulaChecks
open NumberedWindowPresentationCheckers NumberedWindowInternalPresentationTargets
open NumberedWindowInternalLeastChecks NumberedWindowPresentationLeast NumberedWindowPresentationClauses
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.SourcePresentation ID1Completion.InternalCalculus

theorem exact_ConcreteLeastInterpretation : ConcreteLeastInterpretation := by
  intro xs s
  obtain ⟨i,j,r,d,heval,hinterp⟩ := exact_ConcretePresentation xs s
  refine ⟨i,j,r,d,heval,?_⟩
  intro context
  let p := standardLeastPredicate (sourceBody (data i j r d) context)
  have same : ∀ z, p z ↔ least (checks xs s) z :=
    exact_LeastTransport _ _ (fun P => (hinterp context P).1)
  have eq : p = least (checks xs s) := funext fun z => propext (same z)
  refine ⟨same,?_⟩
  exact ((hinterp context p).2).trans (by rw [eq])

#print axioms exact_ConcreteLeastInterpretation
end LogicLineages.PersistentMarking.NumberedWindowConcreteLeastChecks
