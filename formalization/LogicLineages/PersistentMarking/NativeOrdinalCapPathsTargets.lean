import LogicLineages.PersistentMarking.NativeOrdinalBasisChecks

namespace LogicLineages.PersistentMarking.NativeOrdinalCapPathsTargets
open Spine NativeIndexedCarrierTargets NativeIteratorStrictTargets
open NativeOrdinalBasisTargets

/-- An exactly indexed path in the original confined comparison. In particular, the cap
edge and the outer-argument selection do not have to be reductions. -/
inductive StrictPath (S : Signature) :
    Nat → ClosedNativeTerm S indexType → ClosedNativeTerm S indexType → Prop
  | nil (a) : StrictPath S 0 a a
  | cons {n a b c} : NativeBelow b a → StrictPath S n b c → StrictPath S (n + 1) a c

def closedSuccessor (S : Signature) : ClosedNativeTerm S (.arrow indexType indexType) :=
  ⟨ordinalSuccessor, (NativeOrdinalBasisChecks.exact_ClosedOrdinalBasis S).2.1⟩

def closedZero (S : Signature) : ClosedNativeTerm S indexType :=
  ⟨ordinalZero, (NativeOrdinalBasisChecks.exact_ClosedOrdinalBasis S).1⟩

def closedOmega (S : Signature) : ClosedNativeTerm S indexType :=
  ⟨omegaCarrier, (NativeOrdinalBasisChecks.exact_ClosedOrdinalBasis S).2.2⟩

def ExactSuccessorIterationPath : Prop :=
  ∀ S (u : ClosedNativeTerm S indexType) m,
    StrictPath S (2 * m) (finiteApplication (closedSuccessor S) u m) u

def ExactCapPayloadPath : Prop :=
  ∀ S (u : ClosedNativeTerm S indexType) m,
    StrictPath S (2 * m + 1) (cap (closedSuccessor S) u) u

def ExactOmegaZeroPath : Prop :=
  ∀ S m, StrictPath S (2 * m + 1) (closedOmega S) (closedZero S)

end LogicLineages.PersistentMarking.NativeOrdinalCapPathsTargets
