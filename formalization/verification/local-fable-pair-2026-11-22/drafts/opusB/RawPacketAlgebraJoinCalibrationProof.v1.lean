module
public import LogicLineages.PermittedControl.RawPacketAlgebraJoinTargets

public section
namespace LogicLineages.PermittedControl.RawPacketAlgebra
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection (LowerOperand LowerOperandCode PreparedPacketCode preparedPacketCode
  preparedTableBytes)
open ActualPreparedSlotAppend (Packet append shift shiftName shiftSummand shiftRow shiftAtom)
open ActualSignedRouteCartesian (choices tuplePacket)

theorem nameShift (d n : Nat) : shiftNameCode d n = shiftName d n := by
  cases n with
  | zero => rfl
  | succ n => simp [shiftNameCode,shiftName]

theorem itemShift (d : Nat) (s : NormalForm.Summand) :
    shiftItemCode d s.data = (shiftSummand d s).data := by
  cases s with
  | variable i => exact congrArg (fun n => ((0 : Nat),n,(0 : Int),(0 : Int))) (nameShift d i)
  | phi i e => exact congrArg (fun n => ((1 : Nat),n,e,(0 : Int))) (nameShift d i)
  | hyperPhi i e h => exact congrArg (fun n => ((2 : Nat),n,e,h)) (nameShift d i)

theorem rowShift (d : Nat) (r : NormalForm.Row) :
    shiftRowCode d (NormalForm.rowData r) = NormalForm.rowData (shiftRow d r) := by
  simp only [shiftRowCode,NormalForm.rowData,shiftRow,List.map_map,Function.comp_def,itemShift]

theorem dataShift (d : Nat) (a : NormalForm.Atom) :
    shiftAtomData d a.data = (shiftAtom d a).data := by
  cases a with
  | nonnegative r => exact congrArg (fun x => ((0 : Nat),(0 : Nat),x)) (rowShift d r)
  | divisible m r => exact congrArg (fun x => ((1 : Nat),m,x)) (rowShift d r)

theorem atomShift (d : Nat) (a : NormalForm.Atom) :
    shiftAtomCode d (Encodable.encode a.data) = Encodable.encode (shiftAtom d a).data := by
  have dec : LinearRows.Code.decodeAtom (Encodable.encode a.data) = a.data := by
    simp only [LinearRows.Code.decodeAtom,Encodable.encodek,Option.getD_some]
  unfold shiftAtomCode
  rw [dec]
  exact congrArg Encodable.encode (dataShift d a)

private theorem mapAtoms_step (op : Nat → Nat) (payload tag : Nat) (ht : tag < 6) :
    LinearRows.Code.mapAtoms op (6 * payload + tag) =
      if tag = 0 then 0 else if tag = 1 then 1
      else if tag = 2 then 6 * op payload + 2
      else if tag = 3 then 6 * LinearRows.Code.mapAtoms op payload + 3
      else 6 * Nat.pair (LinearRows.Code.mapAtoms op payload.unpair.1)
        (LinearRows.Code.mapAtoms op payload.unpair.2) + tag := by
  have hm : (6 * payload + tag) % 6 = tag := by omega
  have hd : (6 * payload + tag) / 6 = payload := by omega
  rw [LinearRows.Code.mapAtoms,hm,hd]

theorem shiftMapAtoms (d : Nat) (p : NormalForm.Formula) :
    LinearRows.Code.mapAtoms (shiftAtomCode d) p.encode = (shift d p).encode := by
  induction p with
  | truth =>
      simpa [NormalForm.Formula.encode,shift] using mapAtoms_step (shiftAtomCode d) 0 0 (by decide)
  | falsity =>
      simpa [NormalForm.Formula.encode,shift] using mapAtoms_step (shiftAtomCode d) 0 1 (by decide)
  | atom a =>
      simpa [NormalForm.Formula.encode,shift,atomShift] using
        mapAtoms_step (shiftAtomCode d) (Encodable.encode a.data) 2 (by decide)
  | negative p hp =>
      simpa [NormalForm.Formula.encode,shift,hp] using
        mapAtoms_step (shiftAtomCode d) p.encode 3 (by decide)
  | conjunction p q hp hq =>
      simpa [NormalForm.Formula.encode,shift,Nat.unpair_pair,hp,hq] using
        mapAtoms_step (shiftAtomCode d) (Nat.pair p.encode q.encode) 4 (by decide)
  | disjunction p q hp hq =>
      simpa [NormalForm.Formula.encode,shift,Nat.unpair_pair,hp,hq] using
        mapAtoms_step (shiftAtomCode d) (Nat.pair p.encode q.encode) 5 (by decide)

theorem shiftCodeEq (d : Nat) (p : NormalForm.Formula) :
    shiftCode d p.encode = (shift d p).encode := shiftMapAtoms d p

theorem exactShiftCode : ExactShiftCode := shiftCodeEq

theorem tableBytes (t : List LowerOperand) : tableOf (preparedTableBytes t) = t.map LowerOperand.code := by
  simp only [tableOf,preparedTableBytes,Encodable.encodek,Option.getD_some]

theorem appendCodeEq (l r : Packet) :
    appendCode (encodePacket l) (encodePacket r) = encodePacket (append l r) := by
  change (Encodable.encode (tableOf (preparedTableBytes l.1) ++ tableOf (preparedTableBytes r.1)),
      LinearRows.Code.conjunction l.2.encode
        (shiftCode (tableOf (preparedTableBytes l.1)).length r.2.encode)) =
    (preparedTableBytes (l.1 ++ r.1),(NormalForm.Formula.conjunction l.2 (shift l.1.length r.2)).encode)
  rw [tableBytes,tableBytes,List.length_map,shiftCodeEq]
  simp only [preparedTableBytes,List.map_append]
  try rfl

theorem exactAppendCode : ExactAppendCode := appendCodeEq

theorem tupleCodeEq (ps : List Packet) :
    tupleCode (ps.map encodePacket) = encodePacket (tuplePacket ps) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    change appendCode (encodePacket p) (tupleCode (ps.map encodePacket)) =
      encodePacket (append p (tuplePacket ps))
    rw [ih]
    exact appendCodeEq p (tuplePacket ps)

theorem exactTupleCode : ExactTupleCode := tupleCodeEq

theorem choicesCodeEq (rows : List (List Packet)) :
    choicesCode (rows.map (List.map encodePacket)) = (choices rows).map (List.map encodePacket) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    change (row.map encodePacket).flatMap
        (fun c => (choicesCode (rows.map (List.map encodePacket))).map (List.cons c)) =
      (row.flatMap (fun p => (choices rows).map (List.cons p))).map (List.map encodePacket)
    rw [ih]
    first
      | simp only [List.flatMap_map,List.map_flatMap,List.map_map,Function.comp_def,List.map_cons]
      | simp [List.flatMap_map,List.map_flatMap,Function.comp_def]

theorem exactChoicesCode : ExactChoicesCode := choicesCodeEq

theorem joinCodeEq (rows : List (List Packet)) :
    joinCode (rows.map (List.map encodePacket)) = ((choices rows).map tuplePacket).map encodePacket := by
  change (choicesCode (rows.map (List.map encodePacket))).map tupleCode = _
  rw [choicesCodeEq rows,List.map_map,List.map_map]
  apply List.map_congr_left
  intro ps _
  exact tupleCodeEq ps

theorem exactJoinCode : ExactJoinCode := joinCodeEq

theorem joinCalibration : JoinCalibration :=
  ⟨exactShiftCode,exactAppendCode,exactTupleCode,exactChoicesCode,exactJoinCode⟩

#print axioms joinCalibration

end LogicLineages.PermittedControl.RawPacketAlgebra
