import LogicLineages.PersistentMarking.NativeOrdinalRepeatedCapBlockTargets
import LogicLineages.PersistentMarking.NativeOrdinalCapPathsProof

namespace LogicLineages.PersistentMarking.NativeOrdinalRepeatedCapBlockProof
open Spine NativeIndexedCarrierTargets NativeIteratorStrictTargets
open NativeOrdinalBasisTargets NativeOrdinalBasisChecks NativeOrdinalCapPathsTargets
open NativeOrdinalCapPathsProof NativeOrdinalRepeatedCapBlockTargets

/-- Fusion of the very same repeated native application, keeping the
original starting term and every literal intermediate occurrence. -/
theorem finiteSuccessorFusion (S : Signature) (u : ClosedNativeTerm S indexType) (m d : Nat) :
    finiteApplication (closedSuccessor S) u (m + d) =
      finiteApplication (closedSuccessor S) (finiteApplication (closedSuccessor S) u m) d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change NativeClosedApplication.applyClosed (closedSuccessor S)
      (finiteApplication (closedSuccessor S) u (m + d)) =
      NativeClosedApplication.applyClosed (closedSuccessor S)
        (finiteApplication (closedSuccessor S) (finiteApplication (closedSuccessor S) u m) d)
    exact congrArg (NativeClosedApplication.applyClosed (closedSuccessor S)) ih

private theorem splice {S : Signature} {length₁ length₂ : Nat}
    {a b c : ClosedNativeTerm S indexType}
    (first : StrictPath S length₁ a b) (last : StrictPath S length₂ b c) :
    StrictPath S (length₂ + length₁) a c := by
  revert last
  induction first with
  | nil q => intro last; exact last
  | cons step _ ih =>
    intro last
    exact .cons step (ih last)

theorem exact_WithinBlockPaths : ExactWithinBlockPaths := by
  intro S u k m d
  have aligned : blockNode S u k (m + (d + 1)) =
      finiteApplication (closedSuccessor S) (blockNode S u k m) (d + 1) :=
    finiteSuccessorFusion S (capStage S u k) m (d + 1)
  rw [aligned]
  exact exact_SuccessorIterationPath S (blockNode S u k m) (d + 1)

private theorem capStageToOlderOccurrence (S : Signature) (u : ClosedNativeTerm S indexType)
    (k m d : Nat) :
    StrictPath S (d + 1) (capStage S u (k + (d + 1))) (blockNode S u k m) := by
  induction d with
  | zero =>
    exact .cons (exact_CapAboveFiniteApplications S indexType (closedSuccessor S) (capStage S u k) m).2
      (.nil (blockNode S u k m))
  | succ d ih =>
    let old := capStage S u (k + (d + 1))
    have edge : NativeBelow old (cap (closedSuccessor S) old) :=
      (exact_CapAboveFiniteApplications S indexType (closedSuccessor S) old 0).2
    exact .cons edge ih

theorem exact_AcrossBlockPaths : ExactAcrossBlockPaths := by
  intro S u k m d n
  have first : StrictPath S (2 * n) (blockNode S u (k + (d + 1)) n)
      (capStage S u (k + (d + 1))) :=
    exact_SuccessorIterationPath S (capStage S u (k + (d + 1))) n
  have path := splice first (capStageToOlderOccurrence S u k m d)
  rw [Nat.add_comm (2 * n) (d + 1)]
  exact path

theorem exact_ZeroOmegaOrigins : ExactZeroOmegaOrigins := by
  intro S
  exact ⟨rfl, Subtype.ext rfl⟩

#print axioms exact_WithinBlockPaths
#print axioms exact_AcrossBlockPaths
#print axioms exact_ZeroOmegaOrigins

end LogicLineages.PersistentMarking.NativeOrdinalRepeatedCapBlockProof
