module
public import LogicLineages.PersistentMarking.NumberedWindowConcreteGuardedGraphTargets
import LogicLineages.PersistentMarking.NumberedWindowConcreteFunctionalGraphChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalAccessibilityChecks
import LogicLineages.PersistentMarking.NumberedWindowGuardedGraphChecks
public section
namespace LogicLineages.PersistentMarking.NumberedWindowConcreteGuardedGraphChecks
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowAddressApplication NumberedWindowAddressAlgorithm
open NumberedWindowScalarAlgorithm (Settings scalar canonical)
open NumberedWindowConcreteGuardedGraphTargets NumberedWindowGuardedGraphTargets
open NumberedWindowGuardedGraphChecks

private theorem inputs (s : Settings) (f u v : Nat) (h : graph s f u v = true) :
    scalar s f = true ∧ scalar s u = true := by
  have value : application s f u = some v := eq_of_beq h
  cases hf : addressView f with
  | none => simp [application,hf] at value
  | some F =>
    cases hu : addressView u with
    | none => simp [application,hf,hu] at value
    | some U =>
      simp only [application,hf,hu,Option.bind_some] at value
      change applyAddresses s F U = some v at value
      unfold applyAddresses at value
      cases ht : arrowView F.2.1 with
      | none => simp [ht] at value
      | some pair =>
        rw [ht] at value
        cases hf' : canonical s F <;> cases hu' : canonical s U <;>
          simp [hf',hu'] at value <;> simp [scalar,hf,hu,hf',hu']

theorem exact_ConcreteGuardedApplication : ConcreteGuardedApplication := by
  intro xs s
  obtain ⟨i,j,r,d,he,hi,hr⟩ :=
    NumberedWindowInternalAccessibilityChecks.exact_ConcreteInternalAccessibility xs s
  obtain ⟨_,p,_,hp,_,unique⟩ :=
    NumberedWindowConcreteFunctionalGraphChecks.exact_ConcreteFunctionalApplication s
  obtain ⟨both,inheritUnique⟩ := exact_GuardRules i j r d p
  refine ⟨i,j,r,d,NumberedWindowGuardedGraphTargets.guard i p,he,hi,hr,?_,inheritUnique unique,both⟩
  intro f u v
  rw [exact_GuardEvaluation,he.1,he.1,hp]
  change (if (scalar s f).toNat = 1 ∧ (scalar s u).toNat = 1 ∧ (graph s f u v).toNat = 1 then 1 else 0) = _
  cases h : graph s f u v with
  | false => simp
  | true => obtain ⟨hf,hu⟩ := inputs s f u v h; simp [hf,hu]
#print axioms exact_ConcreteGuardedApplication
end LogicLineages.PersistentMarking.NumberedWindowConcreteGuardedGraphChecks
