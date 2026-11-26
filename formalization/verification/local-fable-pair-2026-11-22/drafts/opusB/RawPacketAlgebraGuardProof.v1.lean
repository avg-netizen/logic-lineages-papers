module
public import LogicLineages.PermittedControl.RawPacketAlgebraGuardTargets
import LogicLineages.PermittedControl.RawPacketAlgebraJoinCalibrationProof
import LogicLineages.PermittedControl.RawPacketAlgebraJoinEffectivityProof
import LogicLineages.PermittedControl.PreparedParameterCodeProof
import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof

public section
namespace LogicLineages.PermittedControl.RawPacketAlgebra
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OrdinalComparison.LayeredComparison.IntegerAlgorithms.Proof (ofNat_primitive negate_primitive)
open PreparedProjection (LowerOperandCode LongFieldCode PreparedPacketCode eliminatePreparedCode
  preparedProjectionCodeExact)
open ActualPreparedSlotAppend (Packet)
open ActualSelectedSignedRouteProjection (cutoffPacket bounded project)
open ActualSymbolicPredecessorProjection (predecessorPacket prepend)

theorem predecessorCodeEq (top : Nat) : predecessorCode top = encodePacket (predecessorPacket top) := rfl

theorem exactPredecessorCode : ExactPredecessorCode := predecessorCodeEq

theorem prependCodeEq (top : Nat) (p : Packet) :
    prependCode top (encodePacket p) = encodePacket (prepend top p) := by
  by_cases zero : top = 0
  · rw [prependCode,if_pos zero,prepend,if_pos zero]
  · rw [prependCode,if_neg zero,prepend,if_neg zero,predecessorCodeEq]
    exact appendCodeEq _ _

theorem exactPrependCode : ExactPrependCode := prependCodeEq

theorem cutoffCodeEq (minimum : Nat) : cutoffCode minimum = encodePacket (cutoffPacket minimum) := rfl

theorem exactCutoffCode : ExactCutoffCode := cutoffCodeEq

theorem boundedCodeEq (minimum : Nat) (p : Packet) :
    boundedCode minimum (encodePacket p) = encodePacket (bounded minimum p) := by
  change appendCode (cutoffCode minimum) (encodePacket p) = _
  rw [cutoffCodeEq]
  exact appendCodeEq _ _

theorem exactBoundedCode : ExactBoundedCode := boundedCodeEq

theorem projectCodeEq (minimum : Nat) (p : Packet) :
    projectCode minimum (encodePacket p) = encodePacket (project minimum p) := by
  change eliminatePreparedCode (boundedCode minimum (encodePacket p)) = _
  rw [boundedCodeEq]
  exact preparedProjectionCodeExact.2.2.2 (bounded minimum p).1 (bounded minimum p).2

theorem exactProjectCode : ExactProjectCode := projectCodeEq

theorem guardCalibration : GuardCalibration :=
  ⟨exactPredecessorCode,exactPrependCode,exactCutoffCode,exactBoundedCode,exactProjectCode⟩

theorem predecessorPrimitive : Primrec predecessorCode := by
  have op : Primrec (fun top : Nat =>
      (((0 : Nat),top-1,((0 : Nat),(0 : Nat),(0 : Nat),(0 : Nat))) : LowerOperandCode)) :=
    (Primrec.const 0).pair ((Primrec.nat_sub.comp Primrec.id (Primrec.const 1)).pair (Primrec.const _))
  have table : Primrec (fun top : Nat => Encodable.encode
      ([((0 : Nat),top-1,((0 : Nat),(0 : Nat),(0 : Nat),(0 : Nat)))] : List LowerOperandCode)) :=
    Primrec.encode.comp (Primrec.list_cons.comp op (Primrec.const []))
  exact table.pair (Primrec.const _)

theorem cutoffPrimitive : Primrec cutoffCode := by
  have neg : Primrec (fun m : Nat => -(m : Int)) := negate_primitive.comp ofNat_primitive
  have data : Primrec (fun m : Nat => (((0 : Nat),(0 : Nat),(-(m : Int),
      [((1 : Int),((0 : Nat),(0 : Nat),(0 : Int),(0 : Int)))])) : NormalForm.Code.AtomData)) :=
    (Primrec.const 0).pair ((Primrec.const 0).pair (neg.pair (Primrec.const _)))
  have code : Primrec (fun m : Nat => 6 * Encodable.encode (((0 : Nat),(0 : Nat),(-(m : Int),
      [((1 : Int),((0 : Nat),(0 : Nat),(0 : Int),(0 : Int)))])) : NormalForm.Code.AtomData) + 2) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) (Primrec.encode.comp data))
      (Primrec.const 2)
  exact (Primrec.const _).pair code

theorem prependPrimitive : Primrec₂ prependCode :=
  Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) Primrec.snd
    (appendPrimitive.comp (predecessorPrimitive.comp Primrec.fst) Primrec.snd)

theorem boundedPrimitive : Primrec₂ boundedCode :=
  appendPrimitive.comp (cutoffPrimitive.comp Primrec.fst) Primrec.snd

theorem projectPrimitive : Primrec₂ projectCode := by
  have elim : Primrec eliminatePreparedCode := preparedProjectionCodeExact.1
  exact elim.comp boundedPrimitive

theorem guardEffectivity : GuardEffectivity :=
  ⟨predecessorPrimitive,prependPrimitive,cutoffPrimitive,boundedPrimitive,projectPrimitive⟩

theorem fullRawPacketAlgebraGuard : FullRawPacketAlgebraGuard := ⟨guardCalibration,guardEffectivity⟩

#print axioms fullRawPacketAlgebraGuard

end LogicLineages.PermittedControl.RawPacketAlgebra
