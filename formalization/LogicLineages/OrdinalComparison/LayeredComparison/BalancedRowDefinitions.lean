module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedNumericalDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedRow
/-- A literal heterogeneous source atom; its complete norm argument contains
EVERY entry of the whole common basis positively. -/
structure Atom where
  head:NONote
  offset:Nat
  coefficients:List Nat

/-- Entire signed comparison row, INCLUDING the outside lower-layer remainder.
The same actual basis list is supplied to every atom and the remainder. -/
structure Row where
  constant:Int
  remainder:List Int
  atoms:List (Int×Atom)

def maximum (xs:List Nat):Nat:=xs.foldr max 0
noncomputable def normOffset (a:Atom):Nat:=actualOrdinalNorm a.head.1.repr+a.offset
noncomputable def input (basis:List Nat) (a:Atom):Nat:=
  normOffset a+(a.coefficients.zipWith (·*·) basis).sum

def coefficientMass (row:Row):Nat:=(row.atoms.map (fun a=>a.1.natAbs)).sum
def outsideMaximum (row:Row):Nat:=maximum (row.remainder.map Int.natAbs)
def multiplierMaximum (row:Row):Nat:=max 1 (maximum (row.atoms.flatMap (fun a=>a.2.coefficients)))
noncomputable def offsetMaximum (row:Row):Nat:=maximum (row.atoms.map (fun a=>normOffset a.2))
noncomputable def normMaximum (row:Row):Nat:=maximum (row.atoms.map (fun a=>actualOrdinalNorm a.2.head.1.repr))

/-- Exactly balanced-L, computed BEFORE any cancellation from the original row. -/
noncomputable def threshold (row:Row):Nat:=BalancedNumerical.threshold row.constant
  (coefficientMass row) (outsideMaximum row) (multiplierMaximum row) (offsetMaximum row) (normMaximum row)

def wellFormed (basis:List Nat) (row:Row):Prop:=row.remainder.length=basis.length∧
  ∀a∈row.atoms,a.2.coefficients.length=basis.length∧∀c∈a.2.coefficients,1≤c

def remainderValue (basis:List Nat) (row:Row):Int:=row.constant+
  (row.remainder.zipWith (fun r b=>r*(b:Int)) basis).sum

noncomputable def value (basis:List Nat) (row:Row):Int:=remainderValue basis row+
  (row.atoms.map (fun a=>a.1*(actualHeadValue a.2.head.1.repr (input basis a.2):Int))).sum
end LogicLineages.OrdinalComparison.LayeredComparison.BalancedRow
