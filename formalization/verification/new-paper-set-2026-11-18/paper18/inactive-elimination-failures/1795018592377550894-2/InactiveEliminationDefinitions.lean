module
public import LogicLineages.StandardControlCurrent.OrderedOccurrenceDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeDefinitions
@[expose] public section
namespace LogicLineages.StandardControlCurrent.InactiveElimination
open OrdinalComparison LayeredComparison.SnyatkovCompletion NormalForm

/-- Erase numerical zero contributions only. Existing domain guards are ordinary
separate atoms and remain at their original Boolean positions. -/
def cleanRow (r : Row) : Row := (r.1,r.2.filter (fun a => a.1 != 0))
def cleanAtom : Atom → Atom
  | .nonnegative r => .nonnegative (cleanRow r)
  | .divisible m r => .divisible m (cleanRow r)
def clean : Formula → Formula
  | .truth => .truth
  | .falsity => .falsity
  | .atom a => .atom (cleanAtom a)
  | .negative p => .negative (clean p)
  | .conjunction p q => .conjunction (clean p) (clean q)
  | .disjunction p q => .disjunction (clean p) (clean q)
def eliminate (i : Nat) (p : Formula) : Formula := LinearRows.eliminate i (clean p)
def candidates (u : LinearRows.UnitFormula) : List Row :=
  (LinearRows.cutoffs u).flatMap (fun b => (List.range (LinearRows.period u)).map
    (fun j => LinearRows.rowAdd b (LinearRows.rowConst (j : Int))))
namespace Code
def cleanAtom (n : Nat) : Nat :=
  let a := LinearRows.Code.decodeAtom n
  Encodable.encode (a.1,a.2.1,a.2.2.1,a.2.2.2.filter (fun z => z.1 != 0))
def clean (n : Nat) : Nat := LinearRows.Code.mapAtoms cleanAtom n
def eliminate (i n : Nat) : Nat := LinearRows.Code.eliminate i (clean n)
end Code
end LogicLineages.StandardControlCurrent.InactiveElimination
