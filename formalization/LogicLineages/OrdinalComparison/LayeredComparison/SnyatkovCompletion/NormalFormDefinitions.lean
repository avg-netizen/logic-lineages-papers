module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HyperWindowCodeDefinitions
public import Mathlib.Computability.Primrec.Basic
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NormalForm

/-- The literal three summand kinds of the source normal form. In particular
there is no nested H, arbitrary observer or supplied semantic evaluator. -/
inductive Summand where
  | variable (i : Nat)
  | phi (i : Nat) (shift : Int)
  | hyperPhi (i : Nat) (indexShift outerShift : Int)

def Summand.name : Summand → Nat
  | .variable i | .phi i _ | .hyperPhi i _ _ => i
def Summand.term : Summand → Term
  | .variable i => .variable i
  | .phi i e => .phi (shiftTerm (.variable i) e)
  | .hyperPhi i e h => HyperWindow.valueTerm i e h
def Summand.meaningful (s : Summand) (ν : Nat → Nat) : Prop :=
  match s with
  | .variable _ => True
  | .phi i e => 0 ≤ (ν i : Int) + e
  | .hyperPhi i e h => 0 ≤ (ν i : Int) + e ∧
      0 ≤ (FixedSeedControlResidue.H (((ν i : Int) + e).toNat) : Int) + h

def hyperRequired (h : Int) : Nat := (-h).toNat
/-- The below-H(0)=1 case must be separate: its least index is zero, whereas
the source floor inverse defaults to zero below its first range point. -/
def hyperThreshold (h : Int) : Nat :=
  if hyperRequired h ≤ 1 then 0 else SnyatkovInverse.hyperInverse (hyperRequired h - 1) + 1
def Summand.domainCutoff : Summand → Nat
  | .variable _ => 0
  | .phi _ e => (-e).toNat
  | .hyperPhi _ e h => ((hyperThreshold h : Int) - e).toNat

/-- Finite OCCURRENCE list, not a map choosing one coefficient per name.
Repeated names/shifts and all zero/cancelled weights remain original data. -/
abbrev Row := Int × List (Int × Summand)

def rowValue (row : Row) (ν : Nat → Nat) : Int :=
  row.1 + (row.2.map (fun a => a.1 * (a.2.term.value ν : Int))).sum
def rowVariables (row : Row) : List Nat := row.2.map (fun a => a.2.name)
def rowMeaningful (row : Row) (ν : Nat → Nat) : Prop := ∀ a ∈ row.2, a.2.meaningful ν

def positiveTerm (row : Row) : Term :=
  .add (.numeral row.1.toNat) (row.2.foldr (fun a rest =>
    .add (.multiply a.1.toNat a.2.term) rest) (.numeral 0))
def negativeTerm (row : Row) : Term :=
  .add (.numeral (-row.1).toNat) (row.2.foldr (fun a rest =>
    .add (.multiply (-a.1).toNat a.2.term) rest) (.numeral 0))
def absoluteTerm (row : Row) : Term :=
  .add (.subtract (positiveTerm row) (negativeTerm row))
    (.subtract (negativeTerm row) (positiveTerm row))

/-- Domains lower to PURE LINEAR rows, with no live H term in the guard.
The exact cutoff theorem is unpaid until proved against these definitions. -/
def domainRow (s : Summand) : Row := (-(s.domainCutoff : Int), [(1, .variable s.name)])

inductive Atom where
  | nonnegative (row : Row)
  | divisible (modulusMinusOne : Nat) (row : Row)
def Atom.row : Atom → Row
  | .nonnegative row | .divisible _ row => row
def Atom.eval (a : Atom) (ν : Nat → Nat) : Prop :=
  match a with
  | .nonnegative row => 0 ≤ rowValue row ν
  | .divisible m row => ((m + 1 : Nat) : Int) ∣ rowValue row ν
def Atom.compile : Atom → Matrix
  | .nonnegative row => atMost (negativeTerm row) (positiveTerm row)
  | .divisible m row => .divisible (m + 1) (absoluteTerm row)

inductive Formula where
  | truth | falsity
  | atom (a : Atom)
  | negative (p : Formula)
  | conjunction (p q : Formula)
  | disjunction (p q : Formula)
def Formula.eval (p : Formula) (ν : Nat → Nat) : Prop :=
  match p with
  | .truth => True
  | .falsity => False
  | .atom a => a.eval ν
  | .negative q => ¬q.eval ν
  | .conjunction q r => q.eval ν ∧ r.eval ν
  | .disjunction q r => q.eval ν ∨ r.eval ν
def Formula.compile : Formula → Matrix
  | .truth => .truth
  | .falsity => .falsity
  | .atom a => a.compile
  | .negative p => .negative p.compile
  | .conjunction p q => .conjunction p.compile q.compile
  | .disjunction p q => .disjunction p.compile q.compile
def Formula.variables : Formula → List Nat
  | .truth | .falsity => []
  | .atom a => rowVariables a.row
  | .negative p => p.variables
  | .conjunction p q | .disjunction p q => p.variables ++ q.variables

/-- Original domains are materialized at their ACTUAL Boolean position by
the caller. They are not silently imposed as one new global-tail assumption. -/
def domainFormula (row : Row) : Formula :=
  row.2.foldr (fun a rest => .conjunction (.atom (.nonnegative (domainRow a.2))) rest) .truth
def guardedAtom (a : Atom) : Formula := .conjunction (domainFormula a.row) (.atom a)

namespace Code
abbrev ItemData := Nat × (Nat × (Int × Int))
abbrev RowData := Int × List (Int × ItemData)
abbrev AtomData := Nat × (Nat × RowData)

def itemTerm (s : ItemData) : Nat :=
  if s.1 = 0 then WindowCode.var s.2.1
  else if s.1 = 1 then WindowCode.phi (WindowCode.shift (WindowCode.var s.2.1) s.2.2.1)
  else HyperWindowCode.value s.2.1 s.2.2.1 s.2.2.2
def itemCutoff (s : ItemData) : Nat :=
  if s.1 = 0 then 0 else if s.1 = 1 then (-s.2.2.1).toNat
  else ((hyperThreshold s.2.2.2 : Int) - s.2.2.1).toNat
def domainRowData (s : ItemData) : RowData :=
  (-(itemCutoff s : Int), [(1, (0, s.2.1, 0, 0))])

def scalarPart (negative : Bool) (z : Int) : Nat := (if negative then -z else z).toNat
def part (negative : Bool) (row : RowData) : Nat :=
  WindowCode.add (WindowCode.numeral (scalarPart negative row.1))
    (row.2.foldr (fun a rest => WindowCode.add
      (WindowCode.multiply (scalarPart negative a.1) (itemTerm a.2)) rest) (WindowCode.numeral 0))
def absolute (row : RowData) : Nat :=
  WindowCode.add (WindowCode.subtract (part false row) (part true row))
    (WindowCode.subtract (part true row) (part false row))
def nonnegative (row : RowData) : Nat := WindowCode.atMost (part true row) (part false row)
def divisible (m : Nat) (row : RowData) : Nat := 8 * Nat.pair (m + 1) (absolute row) + 4
def atom (a : AtomData) : Nat :=
  if a.1 = 0 then nonnegative a.2.2 else divisible a.2.1 a.2.2
def domains (row : RowData) : Nat :=
  row.2.foldr (fun a rest => WindowCode.conjunction (nonnegative (domainRowData a.2)) rest) 0

/-- Total all-code literal Boolean compiler. Invalid atom payloads use a fixed
default; source calibration is stated only for actual encoded source syntax. -/
def formula (code : Nat) : Nat :=
  if code % 6 = 0 then 0
  else if code % 6 = 1 then 1
  else if code % 6 = 2 then atom ((Encodable.decode (code / 6) : Option AtomData).getD (0, 0, (0 : Int), []))
  else if code % 6 = 3 then WindowCode.negative (formula (code / 6))
  else 8 * Nat.pair (formula (code / 6).unpair.1) (formula (code / 6).unpair.2) + (code % 6 + 2)
termination_by code
decreasing_by
  all_goals
    have hpos : 0 < code := by omega
    have hd : code / 6 < code := Nat.div_lt_self hpos (by decide)
    have hl := Nat.unpair_left_le (code / 6)
    have hr := Nat.unpair_right_le (code / 6)
    omega
end Code

def Summand.data : Summand → Code.ItemData
  | .variable i => (0, i, 0, 0)
  | .phi i e => (1, i, e, 0)
  | .hyperPhi i e h => (2, i, e, h)
def rowData (row : Row) : Code.RowData := (row.1, row.2.map (fun a => (a.1, a.2.data)))
def Atom.data : Atom → Code.AtomData
  | .nonnegative row => (0, 0, rowData row)
  | .divisible m row => (1, m, rowData row)
def Formula.encode : Formula → Nat
  | .truth => 0
  | .falsity => 1
  | .atom a => 6 * Encodable.encode a.data + 2
  | .negative p => 6 * p.encode + 3
  | .conjunction p q => 6 * Nat.pair p.encode q.encode + 4
  | .disjunction p q => 6 * Nat.pair p.encode q.encode + 5

def existsPrefix (ν : Nat → Nat) : List Nat → Formula → Prop
  | [], p => p.eval ν
  | i :: rest, p => ∃ n : Nat, existsPrefix (Function.update ν i n) rest p

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NormalForm
