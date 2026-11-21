module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendNumericSourceProof
import LogicLineages.PersistentMarking.NumberedWindowGuardedGraphChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendNumericChecks
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowAddressAlgorithm (addressView)
open NumberedWindowAddressApplication (graph application applyAddresses)
open NumberedWindowScalarAlgorithm (scalar canonical)
open NumberedWindowGuardedGraphChecks (exact_GuardEvaluation)
open NumberedWindowInternalSparseApplicationFrontend (applicationCore applicationGuard)
open NumberedWindowInternalSparseApplicationFrontendTargets
open NumberedWindowInternalSparseApplicationFrontendNumericSourceProof (coreAtViews)


private theorem rejectsNoncanonical (s : NumberedWindowScalarAlgorithm.Settings) (f u y ft ut fk uk : Nat)
    (g d : List Nat) (fv : addressView f = some (g,ft,fk)) (uv : addressView u = some (d,ut,uk))
    (reject : canonical s (g,ft,fk) = false ∨ canonical s (d,ut,uk) = false) :
    graph s f u y = false := by
  cases ar : NumberedWindowAddressApplication.arrowView ft with
  | none => simp [graph,application,fv,uv,applyAddresses,ar]
  | some typed =>
    rcases typed with ⟨dom,cod⟩
    rcases reject with hf | hu
    · simp [graph,application,fv,uv,applyAddresses,ar,hf]
    · simp [graph,application,fv,uv,applyAddresses,ar,hu]

theorem exact_AllInputGuardedApplication : ExactAllInputGuardedApplication := by
  intro s i least hScalar hLeast f u y
  rw [applicationGuard,exact_GuardEvaluation,hScalar f,hScalar u]
  cases fv : addressView f with
  | none => simp [scalar,fv,graph,application]
  | some fa =>
    rcases fa with ⟨g,ft,fk⟩
    cases uv : addressView u with
    | none => simp [scalar,uv,graph,application,fv]
    | some ua =>
      rcases ua with ⟨d,ut,uk⟩
      cases fc : canonical s (g,ft,fk) <;> cases uc : canonical s (d,ut,uk)
      · simp [scalar,fv,uv,fc,uc,rejectsNoncanonical s f u y ft ut fk uk g d fv uv (Or.inl fc)]
      · simp [scalar,fv,uv,fc,uc,rejectsNoncanonical s f u y ft ut fk uk g d fv uv (Or.inl fc)]
      · simp [scalar,fv,uv,fc,uc,rejectsNoncanonical s f u y ft ut fk uk g d fv uv (Or.inr uc)]
      · have left : scalar s f = true := by simp only [scalar,fv,Option.any_some,fc]
        have right : scalar s u = true := by simp only [scalar,uv,Option.any_some,uc]
        rw [left,right]
        change (if 1 = 1 ∧ 1 = 1 ∧ evaluate (applicationCore least) (f ::ᵥ u ::ᵥ y ::ᵥ nil) = 1
          then 1 else 0) = (graph s f u y).toNat
        have same := coreAtViews hLeast f u y ft ut fk uk g d fv uv fc uc
        by_cases original : graph s f u y = true
        · rw [if_pos ⟨rfl,rfl,same.mpr original⟩,original] <;> rfl
        · have rejected : graph s f u y = false := Bool.eq_false_iff.mpr original
          rw [if_neg (fun a => original (same.mp a.2.2)),rejected] <;> rfl

#print axioms exact_AllInputGuardedApplication
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendNumericChecks
