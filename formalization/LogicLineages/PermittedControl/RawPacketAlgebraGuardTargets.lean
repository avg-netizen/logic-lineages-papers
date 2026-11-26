module
public import LogicLineages.PermittedControl.RawPacketAlgebraJoinTargets
public import LogicLineages.PermittedControl.ActualSymbolicPredecessorProjectionTargets

@[expose] public section
namespace LogicLineages.PermittedControl.RawPacketAlgebra
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection (LowerOperandCode PreparedPacketCode eliminatePreparedCode)
open ActualPreparedSlotAppend (Packet)
open ActualSelectedSignedRouteProjection (cutoffPacket bounded project)
open ActualSymbolicPredecessorProjection (predecessorPacket prepend)

/-- Literal code of `predecessorPacket top`: one raw-coordinate slot `top-1`
and the constant row `-1 + x₀ - x₁ ≥ 0`. -/
def predecessorCode (top : Nat) : PreparedPacketCode :=
  (Encodable.encode ([((0 : Nat),top-1,((0 : Nat),(0 : Nat),(0 : Nat),(0 : Nat)))] : List LowerOperandCode),
    NormalForm.Formula.encode (.atom (.nonnegative (-1,[(1,.variable 0),(-1,.variable 1)]))))

def prependCode (top : Nat) (c : PreparedPacketCode) : PreparedPacketCode :=
  if top = 0 then c else appendCode (predecessorCode top) c

/-- Literal code of `cutoffPacket minimum`: empty table, row `-minimum + x₀ ≥ 0`. -/
def cutoffCode (minimum : Nat) : PreparedPacketCode :=
  (Encodable.encode ([] : List LowerOperandCode),
    6 * Encodable.encode (((0 : Nat),(0 : Nat),(-(minimum : Int),
      [((1 : Int),((0 : Nat),(0 : Nat),(0 : Int),(0 : Int)))])) : NormalForm.Code.AtomData) + 2)

def boundedCode (minimum : Nat) (c : PreparedPacketCode) : PreparedPacketCode :=
  appendCode (cutoffCode minimum) c

/-- Chosen-route projection on codes: the accepted kernel `eliminatePreparedCode` (#728). -/
def projectCode (minimum : Nat) (c : PreparedPacketCode) : PreparedPacketCode :=
  eliminatePreparedCode (boundedCode minimum c)

def ExactPredecessorCode : Prop :=
  ∀ top : Nat, predecessorCode top = encodePacket (predecessorPacket top)

def ExactPrependCode : Prop :=
  ∀ (top : Nat) (p : Packet), prependCode top (encodePacket p) = encodePacket (prepend top p)

def ExactCutoffCode : Prop :=
  ∀ minimum : Nat, cutoffCode minimum = encodePacket (cutoffPacket minimum)

def ExactBoundedCode : Prop :=
  ∀ (minimum : Nat) (p : Packet), boundedCode minimum (encodePacket p) = encodePacket (bounded minimum p)

def ExactProjectCode : Prop :=
  ∀ (minimum : Nat) (p : Packet), projectCode minimum (encodePacket p) = encodePacket (project minimum p)

def GuardCalibration : Prop :=
  ExactPredecessorCode ∧ ExactPrependCode ∧ ExactCutoffCode ∧ ExactBoundedCode ∧ ExactProjectCode

def GuardEffectivity : Prop :=
  Primrec predecessorCode ∧ Primrec₂ prependCode ∧ Primrec cutoffCode ∧ Primrec₂ boundedCode ∧
    Primrec₂ projectCode

def FullRawPacketAlgebraGuard : Prop := GuardCalibration ∧ GuardEffectivity

end LogicLineages.PermittedControl.RawPacketAlgebra
