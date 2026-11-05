module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ShiftedInputGuardsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.InactivePhiRows
open NormalForm

/-- A mask marks original occurrences for deletion, without combining weights. -/
def keptItems (mask : List Bool) (xs : List (Int × Summand)) : List (Int × Summand) :=
  ((xs.zip mask).filter (fun a => !a.2)).map Prod.fst
def droppedItems (mask : List Bool) (xs : List (Int × Summand)) : List (Int × Summand) :=
  ((xs.zip mask).filter (fun a => a.2)).map Prod.fst

def remaining (r : Row) (mask : List Bool) : Row := (r.1, keptItems mask r.2)
def dropped (r : Row) (mask : List Bool) : Row := (0, droppedItems mask r.2)
def onlyPhi (r : Row) : Bool := r.2.all (fun a => match a.2 with
  | .phi _ _ => true
  | _ => false)

def admissible (i : Nat) (r : Row) (mask : List Bool) : Bool :=
  (mask.length == r.2.length) && onlyPhi (dropped r mask) &&
    LinearRows.rowLinear i (remaining r mask)

def masks (i : Nat) (r : Row) : List (List Bool) :=
  (CommonHeadLargeGuards.masks r.2.length).filter (admissible i r)
def guard (r : Row) (mask : List Bool) : Formula :=
  ShiftedInputGuards.canceled (dropped r mask)

def withRow : Atom → Row → Atom
  | .nonnegative _, r => .nonnegative r
  | .divisible m _, r => .divisible m r

/-- The guard proves that precisely the deleted subrow is zero. No original
source-domain formula is removed or hoisted by this atomic replacement. -/
def compileAtom (i : Nat) (a : Atom) : Formula :=
  BoundedRows.any ((masks i a.row).map (fun mask =>
    .conjunction (guard a.row mask) (.atom (withRow a (remaining a.row mask)))))

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.InactivePhiRows
