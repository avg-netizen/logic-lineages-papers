module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTuplePresentationProof
import LogicLineages.PersistentMarking.NumberedWindowConcreteFunctionalGraphChecks
import LogicLineages.PersistentMarking.NumberedWindowGuardedGraphChecks

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseTupleApplicationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowScalarAlgorithm (Settings scalar canonical)
open NumberedWindowAddressApplication NumberedWindowAddressAlgorithm
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowFormulaCalibrationTargets (Evaluates)
open NumberedWindowPresentationCheckers (checks)
open NumberedWindowFunctionalGraphTargets (UniqueResult)
open NumberedWindowGuardedGraphTargets (guard InputGuards)
open NumberedWindowGuardedGraphChecks (exact_GuardEvaluation exact_GuardRules)
open NumberedWindowConcreteFunctionalGraphChecks (exact_ConcreteFunctionalApplication)

private theorem actualInputs (s : Settings) (f u v : Nat) (accepted : graph s f u v = true) :
    scalar s f = true ∧ scalar s u = true := by
  have value : application s f u = some v := eq_of_beq accepted
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

theorem guardedValue (xs : Entries) (s : Settings) (i j : Program 1) (r d p₀ : Program 3)
    (values : Evaluates (checks xs s) i j r d)
    (base : ∀ f u v, evaluate p₀ (f ::ᵥ u ::ᵥ v ::ᵥ nil) = (graph s f u v).toNat) :
    ∀ f u v, evaluate (guard i p₀) (f ::ᵥ u ::ᵥ v ::ᵥ nil) = (graph s f u v).toNat := by
  intro f u v
  rw [exact_GuardEvaluation,values.1,values.1,base]
  change (if (scalar s f).toNat = 1 ∧ (scalar s u).toNat = 1 ∧
    (graph s f u v).toNat = 1 then 1 else 0) = _
  cases h : graph s f u v with
  | false => simp
  | true => obtain ⟨hf,hu⟩ := actualInputs s f u v h; simp [hf,hu]

theorem select (xs : Entries) (s : Settings) (i j : Program 1) (r d : Program 3)
    (values : Evaluates (checks xs s) i j r d) :
    ∃ (a : Program 2) (p₀ : Program 3),
      (∀ f u, evaluate a (f ::ᵥ u ::ᵥ nil) = Encodable.encode (application s f u)) ∧
      (∀ f u v, evaluate (guard i p₀) (f ::ᵥ u ::ᵥ v ::ᵥ nil) = (graph s f u v).toNat) ∧
      UniqueResult (guard i p₀) ∧ InputGuards i j r d (guard i p₀) := by
  obtain ⟨a,p₀,ha,hp,_,unique⟩ := exact_ConcreteFunctionalApplication s
  obtain ⟨guards,inheritUnique⟩ := exact_GuardRules i j r d p₀
  exact ⟨a,p₀,ha,guardedValue xs s i j r d p₀ values hp,inheritUnique unique,guards⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseTupleApplicationProof
