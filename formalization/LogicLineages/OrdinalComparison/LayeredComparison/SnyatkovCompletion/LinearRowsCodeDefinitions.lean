module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRows
open NormalForm

namespace Code
abbrev RowData := NormalForm.Code.RowData
abbrev AtomData := NormalForm.Code.AtomData
abbrev UnitAtomData := Nat × (Nat × (Int × RowData))

def rowConst (z : Int) : RowData := (z, [])
def rowAdd (r s : RowData) : RowData := (r.1 + s.1, r.2 ++ s.2)
def rowScale (z : Int) (r : RowData) : RowData :=
  (z * r.1, r.2.map (fun a => (z * a.1, a.2)))
def leading (i : Nat) (r : RowData) : Int :=
  (r.2.map (fun a => if a.2.2.1 = i then a.1 else 0)).sum
def remainder (i : Nat) (r : RowData) : RowData :=
  (r.1, r.2.filter (fun a => a.2.2.1 != i))
def rowLinear (i : Nat) (r : RowData) : Bool :=
  r.2.all (fun a => a.2.1 == 0 || a.2.2.1 != i)
def decodeAtom (payload : Nat) : AtomData :=
  (Encodable.decode payload).getD (0, 0, (0 : Int), [])
def decodeUnit (payload : Nat) : UnitAtomData :=
  (Encodable.decode payload).getD (0, 0, (0 : Int), (0 : Int), [])

/-- A total structural map on the original radix-six Boolean encoding. -/
def mapAtoms (op : Nat → Nat) (code : Nat) : Nat :=
  if code % 6 = 0 then 0 else if code % 6 = 1 then 1
  else if code % 6 = 2 then 6 * op (code / 6) + 2
  else if code % 6 = 3 then 6 * mapAtoms op (code / 6) + 3
  else 6 * Nat.pair (mapAtoms op (code / 6).unpair.1)
    (mapAtoms op (code / 6).unpair.2) + code % 6
termination_by code
decreasing_by
  all_goals
    have hpos : 0 < code := by omega
    have hd : code / 6 < code := Nat.div_lt_self hpos (by decide)
    have hl := Nat.unpair_left_le (code / 6)
    have hr := Nat.unpair_right_le (code / 6)
    omega

def atoms (code : Nat) : List Nat :=
  if code % 6 = 0 then [] else if code % 6 = 1 then []
  else if code % 6 = 2 then [code / 6]
  else if code % 6 = 3 then atoms (code / 6)
  else atoms (code / 6).unpair.1 ++ atoms (code / 6).unpair.2
termination_by code
decreasing_by
  all_goals
    have hpos : 0 < code := by omega
    have hd : code / 6 < code := Nat.div_lt_self hpos (by decide)
    have hl := Nat.unpair_left_le (code / 6)
    have hr := Nat.unpair_right_le (code / 6)
    omega

def isLinear (i code : Nat) : Bool := (atoms code).all (fun a => rowLinear i (decodeAtom a).2.2)
def conjunction (p q : Nat) : Nat := 6 * Nat.pair p q + 4
def unitAtom (a : UnitAtomData) : Nat := 6 * Encodable.encode a + 2
def weight (i : Nat) (a : AtomData) : Nat :=
  if leading i a.2.2 = 0 then 1 else (leading i a.2.2).natAbs
def coefficientModulus (i code : Nat) : Nat :=
  ((atoms code).map (fun a => weight i (decodeAtom a))).prod
def nonzeroSign (z : Int) : Int := if 0 < z then 1 else -1
def adjustAtom (i M : Nat) (a : AtomData) : UnitAtomData :=
  let z := leading i a.2.2
  let r := remainder i a.2.2
  if z = 0 then (a.1, a.2.1, 0, r)
  else let k := M / z.natAbs
    (a.1, if a.1 = 0 then 0 else (a.2.1 + 1) * k - 1,
      nonzeroSign z, rowScale (k : Int) r)
def adjust (i M code : Nat) : Nat :=
  mapAtoms (fun a => Encodable.encode (adjustAtom i M (decodeAtom a))) code
def normalize (i code : Nat) : Nat :=
  let M := coefficientModulus i code
  conjunction (unitAtom (1, M - 1, 1, rowConst 0)) (adjust i M code)
def atomPeriod (a : UnitAtomData) : Nat := if a.1 = 0 then 1 else a.2.1 + 1
def atomCutoffs (a : UnitAtomData) : List RowData :=
  if a.1 = 0 then
    if a.2.2.1 = 1 then [rowScale (-1) a.2.2.2]
    else if a.2.2.1 = -1 then [rowAdd a.2.2.2 (rowConst 1)] else []
  else []
def period (code : Nat) : Nat := ((atoms code).map (fun a => atomPeriod (decodeUnit a))).prod
def cutoffs (code : Nat) : List RowData :=
  rowConst 0 :: (atoms code).flatMap (fun a => atomCutoffs (decodeUnit a))
def instantiateAtom (b : RowData) (a : UnitAtomData) : AtomData :=
  (a.1, a.2.1, rowAdd (rowScale a.2.2.1 b) a.2.2.2)
def instantiate (code : Nat) (b : RowData) : Nat :=
  mapAtoms (fun a => Encodable.encode (instantiateAtom b (decodeUnit a))) code
def guarded (code : Nat) : Nat := conjunction (unitAtom (0, 0, 1, rowConst 0)) code
def unitEliminate (code : Nat) : Nat :=
  BoundedRows.Code.any ((cutoffs code).flatMap (fun b => (List.range (period code)).map
    (fun j => instantiate (guarded code) (rowAdd b (rowConst (j : Int))))))
def eliminate (i code : Nat) : Nat := unitEliminate (normalize i code)
end Code

def UnitAtom.data : UnitAtom → Code.UnitAtomData
  | .nonnegative s r => (0, 0, s.value, rowData r)
  | .divisible m s r => (1, m, s.value, rowData r)
def unitEncode : UnitFormula → Nat
  | .top => 0
  | .bot => 1
  | .atom a => 6 * Encodable.encode a.data + 2
  | .neg p => 6 * unitEncode p + 3
  | .conj p q => 6 * Nat.pair (unitEncode p) (unitEncode q) + 4
  | .disj p q => 6 * Nat.pair (unitEncode p) (unitEncode q) + 5

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRows
