import LogicLineages.PersistentMarking.NativeOrdinalCapPathsTargets

namespace LogicLineages.PersistentMarking.NativeOrdinalCapPathsProof
open Spine NativeReduction NativeIndexedCarrierTargets NativeIteratorStrictTargets
open NativeClosedApplication NativeOrdinalBasisTargets NativeOrdinalBasisChecks
open NativeOrdinalCapPathsTargets

theorem exact_SuccessorIterationPath : ExactSuccessorIterationPath := by
  intro S u m
  induction m with
  | zero =>
    exact .nil u
  | succ n ih =>
    let a := finiteApplication (closedSuccessor S) u n
    obtain ⟨start, mid, startValue, _, _, beta, selectArg⟩ := exact_OrdinalSuccessorSteps S a
    have eq : start = applyClosed (closedSuccessor S) a := Subtype.ext startValue
    have first : NativeBelow mid (applyClosed (closedSuccessor S) a) := by
      rw [← eq]
      exact beta
    have path : StrictPath S ((2 * n + 1) + 1) (applyClosed (closedSuccessor S) a) u :=
      .cons first (.cons selectArg ih)
    have lengthEq : (2 * n + 1) + 1 = 2 * (n + 1) :=
      (Nat.add_assoc (2 * n) 1 1).trans (Nat.mul_succ 2 n).symm
    rw [lengthEq] at path
    exact path

theorem exact_CapPayloadPath : ExactCapPayloadPath := by
  intro S u m
  exact .cons (exact_CapAboveFiniteApplications S indexType (closedSuccessor S) u m).2
    (exact_SuccessorIterationPath S u m)

theorem exact_OmegaZeroPath : ExactOmegaZeroPath := by
  intro S m
  have literal : cap (closedSuccessor S) (closedZero S) = closedOmega S := Subtype.ext rfl
  rw [← literal]
  exact exact_CapPayloadPath S (closedZero S) m

#print axioms exact_SuccessorIterationPath
#print axioms exact_CapPayloadPath
#print axioms exact_OmegaZeroPath

end LogicLineages.PersistentMarking.NativeOrdinalCapPathsProof
