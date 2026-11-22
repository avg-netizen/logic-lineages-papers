module
public import LogicLineages.PermittedControl.ActualSignedRouteCartesianTargets
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.RawPacketAlgebra
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection (LowerOperand LowerOperandCode PreparedPacketCode preparedPacketCode)
open ActualPreparedSlotAppend (Packet append shift)
open ActualSignedRouteCartesian (choices tuplePacket)

/-- The existing packet code (#728): table bytes and formula code. -/
def encodePacket (p : Packet) : PreparedPacketCode := preparedPacketCode p.1 p.2

/-- Operand-code list carried by table bytes (empty on undecodable bytes). -/
def tableOf (bytes : Nat) : List LowerOperandCode :=
  (Encodable.decode bytes : Option (List LowerOperandCode)).getD []

def shiftNameCode (d n : Nat) : Nat := if n = 0 then 0 else d + n

def shiftItemCode (d : Nat) (s : NormalForm.Code.ItemData) : NormalForm.Code.ItemData :=
  (s.1,shiftNameCode d s.2.1,s.2.2)

def shiftRowCode (d : Nat) (r : NormalForm.Code.RowData) : NormalForm.Code.RowData :=
  (r.1,r.2.map (fun a => (a.1,shiftItemCode d a.2)))

def shiftAtomData (d : Nat) (a : NormalForm.Code.AtomData) : NormalForm.Code.AtomData :=
  (a.1,a.2.1,shiftRowCode d a.2.2)

def shiftAtomCode (d payload : Nat) : Nat :=
  Encodable.encode (shiftAtomData d (LinearRows.Code.decodeAtom payload))

/-- Positive-name shift on the radix-six formula code, by the existing atom map. -/
def shiftCode (d code : Nat) : Nat := LinearRows.Code.mapAtoms (shiftAtomCode d) code

def appendCode (l r : PreparedPacketCode) : PreparedPacketCode :=
  (Encodable.encode (tableOf l.1 ++ tableOf r.1),
    LinearRows.Code.conjunction l.2 (shiftCode (tableOf l.1).length r.2))

def unitCode : PreparedPacketCode := encodePacket ([],.truth)

def tupleCode (cs : List PreparedPacketCode) : PreparedPacketCode := cs.foldr appendCode unitCode

def choicesCode : List (List PreparedPacketCode) → List (List PreparedPacketCode)
  | [] => [[]]
  | row::rows => row.flatMap (fun c => (choicesCode rows).map (List.cons c))

/-- Raw join: one joined packet code per Cartesian choice, in literal order. -/
def joinCode (rows : List (List PreparedPacketCode)) : List PreparedPacketCode :=
  (choicesCode rows).map tupleCode

def ExactShiftCode : Prop :=
  ∀ (d : Nat) (p : NormalForm.Formula), shiftCode d p.encode = (shift d p).encode

def ExactAppendCode : Prop :=
  ∀ l r : Packet, appendCode (encodePacket l) (encodePacket r) = encodePacket (append l r)

def ExactTupleCode : Prop :=
  ∀ ps : List Packet, tupleCode (ps.map encodePacket) = encodePacket (tuplePacket ps)

def ExactChoicesCode : Prop :=
  ∀ rows : List (List Packet),
    choicesCode (rows.map (List.map encodePacket)) = (choices rows).map (List.map encodePacket)

def ExactJoinCode : Prop :=
  ∀ rows : List (List Packet),
    joinCode (rows.map (List.map encodePacket)) = ((choices rows).map tuplePacket).map encodePacket

def JoinCalibration : Prop :=
  ExactShiftCode ∧ ExactAppendCode ∧ ExactTupleCode ∧ ExactChoicesCode ∧ ExactJoinCode

def JoinEffectivity : Prop :=
  Primrec₂ shiftCode ∧ Primrec₂ appendCode ∧ Primrec tupleCode ∧ Primrec choicesCode ∧
    Primrec joinCode

def FullRawPacketAlgebraJoin : Prop := JoinCalibration ∧ JoinEffectivity

end LogicLineages.PermittedControl.RawPacketAlgebra
