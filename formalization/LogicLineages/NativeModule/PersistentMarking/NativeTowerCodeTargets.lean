module

public import LogicLineages.NativeModule.PersistentMarking.NativeTowerCodeDefinitions

@[expose] public section

namespace LogicLineages.PersistentMarking.NativeTowerCode
open Spine NativeIndexedCarrierTargets NativeIteratorStrictTargets NativeTowerSequenceTargets

/-- Unconditional primitive recursiveness on natural codes. No `Primcodable Expr`
instance, ordinal calibration, or accessibility supplier is assumed. -/
def SequenceCodePrimitiveRecursive : Prop := Primrec sequenceCode

/-- Translation always succeeds and returns the existing literal term encoding. -/
def SequenceCodeCalibration : Prop :=
  ∀ n, literalCode (sequenceTerm n) = some (sequenceCode n)

/-- The output is the existing `nativeCode` of every closed native representative
of the explicit family, independently of its proof of closed nativeness. -/
def NativeCodeCalibration : Prop :=
  ∀ (S : Signature) (n : Nat) (t : ClosedNativeTerm S indexType),
    t.val = sequenceTerm n → NativeSyntaxCountabilityTargets.nativeCode t = sequenceCode n

def FullTowerCode : Prop :=
  SequenceCodePrimitiveRecursive ∧ SequenceCodeCalibration ∧ NativeCodeCalibration

end LogicLineages.PersistentMarking.NativeTowerCode
