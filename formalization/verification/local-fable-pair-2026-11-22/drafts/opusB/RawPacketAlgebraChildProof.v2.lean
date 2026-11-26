module
public import LogicLineages.PermittedControl.RawPacketAlgebraChildTargets
import LogicLineages.PermittedControl.RawPacketAlgebraGuardProof
import LogicLineages.PermittedControl.RawPacketAlgebraResidualCalibrationProof
import LogicLineages.PermittedControl.RawPacketAlgebraResidualEffectivityProof
import LogicLineages.PermittedControl.RawPacketAlgebraReifyProof

public section
namespace LogicLineages.PermittedControl.RawPacketAlgebra
open PreparedProjection (PreparedPacketCode)
open ActualPreparedSlotAppend (Packet)
open ActualSymbolicPredecessorProjection (prepend)
open ActualGreatestRouteResidual (lowerFamily)
open ActualGuardedResidualBitFamily (reifyFamily)
open ActualBitFamilyRawLayout (RawFamily encodeFamily)

theorem childCodeEq (C top : Nat) (qs : List Packet) :
    childCode (C,top,qs.map encodePacket) =
      encodeFamily (reifyFamily C top (lowerFamily top C (qs.map (prepend top)))) := by
  have pre : (qs.map encodePacket).map (prependCode top) = (qs.map (prepend top)).map encodePacket := by
    rw [List.map_map,List.map_map]
    apply List.map_congr_left
    intro q _
    exact prependCodeEq top q
  change reifyFamilyCode C top (lowerFamilyCode top C ((qs.map encodePacket).map (prependCode top))) = _
  rw [pre,lowerFamilyCodeEq,reifyFamilyCodeEq]

theorem exactChildCode : ExactChildCode := childCodeEq

theorem childPrimitive : Primrec childCode := by
  let X := Nat × Nat × List PreparedPacketCode
  have prepended : Primrec (fun x : X => x.2.2.map (prependCode x.2.1)) :=
    Primrec.list_map (Primrec.snd.comp Primrec.snd)
      (prependPrimitive.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
  have lower : Primrec (fun x : X => lowerFamilyCode x.2.1 x.1 (x.2.2.map (prependCode x.2.1))) :=
    lowerFamilyPrimitive.comp ((Primrec.fst.comp Primrec.snd).pair (Primrec.fst.pair prepended))
  exact reifyFamilyPrimitive.comp (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair lower))

theorem childEffectivity : ChildEffectivity := ⟨childPrimitive,childPrimitive.to_comp⟩

theorem fullRawPacketAlgebraChild : FullRawPacketAlgebraChild := ⟨exactChildCode,childEffectivity⟩

#print axioms exactChildCode
#print axioms fullRawPacketAlgebraChild

end LogicLineages.PermittedControl.RawPacketAlgebra
