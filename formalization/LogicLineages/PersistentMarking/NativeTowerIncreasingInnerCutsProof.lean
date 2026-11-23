import LogicLineages.PersistentMarking.NativeTowerOuterIndexConeProof

namespace LogicLineages.PersistentMarking.NativeTowerIncreasingInnerCutsProof
open Spine NativeIteratorStrictTargets NativeClosedApplication NativeIndexedCarrierTargets NativeIndexedCarrierSubtype
open NativeOrdinalBasisTargets NativeOrdinalBasisChecks NativeOrdinalCapPathsTargets
open NativeTowerWitnessPrefixTargets NativeTowerBetaPathProof
open NativeTowerInnerMapSubstitutionProof NativeTowerInnerMapHigherIteratorProof
open NativeTowerBoundedInnerOrbitBlocksProof NativeTowerOuterIndexConeProof
open NativeIndexedCarrierFiniteOrbitProof NativeIndexedCarrierOrbitBlocksProof

private theorem paidDrainSelectsZero (S : Signature) (l : Nat) :
    ∀ f : ClosedNativeTerm S (ty (l+1)),
        NativeBelow (closedZero S) (applyPaidDrain S (l+1) f) := by
  induction l with
  | zero =>
    intro f
    exact exact_SameTypedNativeApplicationSelect f (paidOperand S 0)
  | succ l ih =>
    intro f
    exact ih (applyClosed f (paidOperand S (l+1)))

/-- No universal inflationarity of the evaluated map is assumed. Literal
Z is its seed at level zero and its final genuine argument at higher levels. -/
theorem exact_OriginalZeroBelowEvaluatedZero (S : Signature) (l : Nat) :
    NativeBelow (closedZero S) (evaluatedInner S l (closedZero S)) := by
  cases l with
  | zero =>
    exact exact_IndexedCarrierFiniteSeedOrbit .base (actualArg S 0)
      (paidOperand S 0) (closedZero S) 0
  | succ l =>
    exact paidDrainSelectsZero S l (printedIndexedHead S (l+1) (closedZero S))

theorem exact_EvaluatedInnerStrictMonotone (S : Signature) (l : Nat) (a b : Base S)
    (smaller : NativeBelow a b) : NativeBelow (evaluatedInner S l a) (evaluatedInner S l b) :=
  exact_OriginalInnerOrbitCrossIndex S l a b smaller 0 0

def evaluatedCutIter (S : Signature) (l : Nat) (a : Base S) : Nat → Base S
  | 0 => a
  | t+1 => evaluatedInner S l (evaluatedCutIter S l a t)

theorem exact_EvaluatedIterRaises (S : Signature) (l : Nat) (a : Base S)
    (starts : NativeBelow a (evaluatedInner S l a)) (n : Nat) :
    NativeBelow (evaluatedCutIter S l a n) (evaluatedCutIter S l a (n+1)) := by
  induction n with
  | zero => exact starts
  | succ n ih => exact exact_EvaluatedInnerStrictMonotone S l _ _ ih

theorem exact_EvaluatedPositiveIterRaises (S : Signature) (l : Nat) (a : Base S)
    (starts : NativeBelow a (evaluatedInner S l a)) (n : Nat) :
    NativeBelow a (evaluatedCutIter S l a (n+1)) := by
  induction n with
  | zero => exact starts
  | succ n ih => exact transBase ih (exact_EvaluatedIterRaises S l a starts (n+1))

theorem exact_EvaluatedCutIterStaysInCone {S l mapping seed}
    (cone : ActualIndexCone S l mapping seed) (a : Base S)
    (admitted : NativeBelow a (actualOuter S mapping seed)) (n : Nat) :
    NativeBelow (evaluatedCutIter S l a n) (actualOuter S mapping seed) := by
  induction n with
  | zero => exact admitted
  | succ n ih => exact exact_EvaluatedInnerStaysInActualCone cone _ ih

/-- Band d has d+1 coordinates; its next start is its actual strict ceiling. -/
def bandStart (S : Signature) (l : Nat) : Nat → Base S
  | 0 => closedZero S
  | d+1 => evaluatedCutIter S l (bandStart S l d) (d+2)

theorem exact_OriginalBandStartRises (S : Signature) (l d : Nat) :
    NativeBelow (bandStart S l d) (evaluatedInner S l (bandStart S l d)) := by
  induction d with
  | zero => exact exact_OriginalZeroBelowEvaluatedZero S l
  | succ d ih =>
    exact exact_EvaluatedIterRaises S l (bandStart S l d) ih (d+2)

theorem exact_OriginalBandStartsAdjacent (S : Signature) (l d : Nat) :
    NativeBelow (bandStart S l d) (bandStart S l (d+1)) :=
  exact_EvaluatedPositiveIterRaises S l _ (exact_OriginalBandStartRises S l d) (d+1)

theorem exact_OriginalBandStartsWeaklyOrdered (S : Signature) (l : Nat)
    {d e : Nat} (ordered : d ≤ e) :
    bandStart S l d = bandStart S l e ∨ NativeBelow (bandStart S l d) (bandStart S l e) := by
  induction ordered with
  | refl => exact Or.inl rfl
  | @step e _ ih =>
    have next := exact_OriginalBandStartsAdjacent S l e
    rcases ih with same | earlier
    · rw [same]
      exact Or.inr next
    · exact Or.inr (transBase earlier next)

theorem exact_OriginalBandStartAdmitted {S l mapping seed}
    (cone : ActualIndexCone S l mapping seed) (d : Nat) :
    NativeBelow (bandStart S l d) (actualOuter S mapping seed) := by
  induction d with
  | zero =>
    have actualOmega : cap (closedSuccessor S) (closedZero S) = closedOmega S := Subtype.ext rfl
    have zeroToOmega : NativeBelow (closedZero S) (closedOmega S) := by
      rw [← actualOmega]
      exact (exact_CapAboveFiniteApplications S indexType (closedSuccessor S) (closedZero S) 0).2
    exact transBase zeroToOmega cone.omegaAdmitted
  | succ d ih => exact exact_EvaluatedCutIterStaysInCone cone (bandStart S l d) ih (d+2)

#print axioms exact_OriginalZeroBelowEvaluatedZero
#print axioms exact_EvaluatedInnerStrictMonotone
#print axioms exact_EvaluatedIterRaises
#print axioms exact_EvaluatedPositiveIterRaises
#print axioms exact_EvaluatedCutIterStaysInCone
#print axioms exact_OriginalBandStartRises
#print axioms exact_OriginalBandStartsAdjacent
#print axioms exact_OriginalBandStartsWeaklyOrdered
#print axioms exact_OriginalBandStartAdmitted

end LogicLineages.PersistentMarking.NativeTowerIncreasingInnerCutsProof
