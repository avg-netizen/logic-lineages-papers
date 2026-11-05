module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.InactivePhiRowsDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ShiftedInputProgramsDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.InactivePhiPrograms.Code

def keptItems (mask : List Bool) (xs : List (Int × NormalForm.Code.ItemData)) :
    List (Int × NormalForm.Code.ItemData) := ((xs.zip mask).filter (fun a => !a.2)).map Prod.fst
def droppedItems (mask : List Bool) (xs : List (Int × NormalForm.Code.ItemData)) :
    List (Int × NormalForm.Code.ItemData) := ((xs.zip mask).filter (fun a => a.2)).map Prod.fst

def remaining (r : NormalForm.Code.RowData) (mask : List Bool) : NormalForm.Code.RowData :=
  (r.1, keptItems mask r.2)
def dropped (r : NormalForm.Code.RowData) (mask : List Bool) : NormalForm.Code.RowData :=
  (0, droppedItems mask r.2)
def onlyPhi (r : NormalForm.Code.RowData) : Bool := r.2.all (fun a => a.2.1 == 1)
def admissible (i : Nat) (r : NormalForm.Code.RowData) (mask : List Bool) : Bool :=
  (mask.length == r.2.length) && onlyPhi (dropped r mask) &&
    LinearRows.Code.rowLinear i (remaining r mask)
def masks (i : Nat) (r : NormalForm.Code.RowData) : List (List Bool) :=
  (CommonHeadLargeGuards.masks r.2.length).filter (admissible i r)
def guard (r : NormalForm.Code.RowData) (mask : List Bool) : Nat :=
  ShiftedInputPrograms.Code.canceled (dropped r mask)
def withRow (a : NormalForm.Code.AtomData) (r : NormalForm.Code.RowData) : NormalForm.Code.AtomData :=
  (a.1, a.2.1, r)
def atom (a : NormalForm.Code.AtomData) : Nat := 6 * Encodable.encode a + 2

def any (ps : List Nat) : Nat := ps.foldr ShiftedInputPrograms.Code.disjunction 1
def compileAtom (i : Nat) (a : NormalForm.Code.AtomData) : Nat :=
  any ((masks i a.2.2).map (fun mask =>
    ShiftedInputPrograms.Code.conjunction (guard a.2.2 mask)
      (atom (withRow a (remaining a.2.2 mask)))))

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.InactivePhiPrograms.Code
