module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.CalibratedPrimary.MembershipNativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.NativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open InternalAcceptanceCalibrationProof NumberedMultisetNumeric
open TwoSol20261113.CalibratedPrimary.Membership

theorem stepEvaluation (head rest reached : Nat) :
    evaluate countStep (head ::ᵥ rest ::ᵥ reached ::ᵥ nil) =
      if head ∈ (decodeNumbers reached).getD [] then rest else rest + 1 := by
  have hc : evaluate (.composition contains ![.projection 2,.projection 0])
      (head ::ᵥ rest ::ᵥ reached ::ᵥ nil) =
      (decide (head ∈ (decodeNumbers reached).getD [])).toNat :=
    TwoSol20261113.CalibratedPrimary.MembershipNativeProof.actualContainsNative reached head
  rw [countStep,evalBranch,evalNormalize,hc]
  by_cases h : head ∈ (decodeNumbers reached).getD []
  · simp only [h,decide_true,Bool.toNat_true,ite_true,Nat.one_ne_zero,ite_false]
    rfl
  · simp only [h,decide_false,Bool.toNat_false,Nat.zero_ne_one,ite_false,ite_true]
    rfl

theorem countFold (xs : List Nat) (reached : Nat) :
    xs.foldr (fun head rest => evaluate countStep (head ::ᵥ rest ::ᵥ reached ::ᵥ nil)) 0 =
      (xs.filter (fun candidate => decide (candidate ∉ (decodeNumbers reached).getD []))).length := by
  induction xs with
  | nil => rfl
  | cons head xs ih =>
    rw [List.foldr_cons,stepEvaluation,ih]
    by_cases h : head ∈ (decodeNumbers reached).getD [] <;>
      simp [List.filter_cons,h]

theorem nativeCount : Targets.NativeCount := by
  intro pool reached
  have h := InternalRawListRecursionEvaluationProof.actualRawListRecursionEvaluation
    1 (InternalAcceptance.constantZero 1) countStep (reached ::ᵥ nil) pool
  change evaluate count (ofFn ![pool,reached]) = _ at h
  rw [h]
  exact countFold _ reached
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryUncoveredCount.NativeProof
