import LogicLineages.PersistentMarking.NativeOrdinalCapPathsTargets

namespace LogicLineages.PersistentMarking.NativeOrdinalRepeatedCapBlockTargets
open Spine NativeIndexedCarrierTargets NativeIteratorStrictTargets
open NativeOrdinalBasisTargets NativeOrdinalCapPathsTargets

/-- Repeat the literal native cap with the original successor, on exactly
the current typed closed payload. -/
def capStage (S : Signature) (u : ClosedNativeTerm S indexType) : Nat → ClosedNativeTerm S indexType
  | 0 => u
  | k + 1 => cap (closedSuccessor S) (capStage S u k)

def blockNode (S : Signature) (u : ClosedNativeTerm S indexType) (k m : Nat) :
    ClosedNativeTerm S indexType :=
  finiteApplication (closedSuccessor S) (capStage S u k) m

/-- One strictly later successor occurrence in the same actual cap block. -/
def ExactWithinBlockPaths : Prop :=
  ∀ S u k m d,
    StrictPath S (2 * (d + 1)) (blockNode S u k (m + (d + 1))) (blockNode S u k m)

/-- From any occurrence of a later cap block to any occurrence of an older
block. The last actual cap edge handles the earlier selected occurrence. -/
def ExactAcrossBlockPaths : Prop :=
  ∀ S u k m d n,
    StrictPath S (2 * n + (d + 1)) (blockNode S u (k + (d + 1)) n) (blockNode S u k m)

/-- The original closed zero starts the family and its first cap is the
same literal omega carrier already used by the manuscript. -/
def ExactZeroOmegaOrigins : Prop :=
  ∀ S, capStage S (closedZero S) 0 = closedZero S ∧
    capStage S (closedZero S) 1 = closedOmega S

end LogicLineages.PersistentMarking.NativeOrdinalRepeatedCapBlockTargets
