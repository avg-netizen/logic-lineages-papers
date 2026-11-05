module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedRowsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SignedRows
open NormalForm

def replacement (j : Nat) (d : Int) (ν : Nat → Nat) : Nat := ((ν j : Int) + d).toNat

/-- A unit-slope translation stays in the three existing summand kinds. -/
def translateSummand (i j : Nat) (d : Int) (s : Summand) : Summand :=
  if s.name = i then
    match s with
    | .variable _ => .variable j
    | .phi _ e => .phi j (d + e)
    | .hyperPhi _ e h => .hyperPhi j (d + e) h
  else s

def offset (i : Nat) (d : Int) : Summand → Int
  | .variable k => if k = i then d else 0
  | .phi _ _ | .hyperPhi _ _ _ => 0

/-- Occurrence order and every coefficient are retained. Only translated
linear occurrences contribute a new integer constant. -/
def rowTranslate (i j : Nat) (d : Int) (row : Row) : Row :=
  (row.1 + (row.2.map (fun a => a.1 * offset i d a.2)).sum,
    row.2.map (fun a => (a.1, translateSummand i j d a.2)))

def atomTranslate (i j : Nat) (d : Int) : Atom → Atom
  | .nonnegative row => .nonnegative (rowTranslate i j d row)
  | .divisible m row => .divisible m (rowTranslate i j d row)

def core (i j : Nat) (d : Int) : Formula → Formula
  | .truth => .truth
  | .falsity => .falsity
  | .atom a => .atom (atomTranslate i j d a)
  | .negative p => .negative (core i j d p)
  | .conjunction p q => .conjunction (core i j d p) (core i j d q)
  | .disjunction p q => .disjunction (core i j d p) (core i j d q)

def anchorDomain (j : Nat) (d : Int) : Formula :=
  .atom (.nonnegative (d, [(1, .variable j)]))

/-- Total signed translation splits at the actual truncation boundary.
Original domain guards are translated at their existing Boolean positions. -/
def substitute (i j : Nat) (d : Int) (p : Formula) : Formula :=
  .disjunction (.conjunction (anchorDomain j d) (core i j d p))
    (.conjunction (.negative (anchorDomain j d)) (BoundedRows.substitute i 0 p))

namespace Code
abbrev ItemData := NormalForm.Code.ItemData
abbrev RowData := NormalForm.Code.RowData
abbrev AtomData := NormalForm.Code.AtomData
abbrev Input := (Nat × Nat) × Int
def input (i j : Nat) (d : Int) : Input := ((i, j), d)

def item (i j : Nat) (d : Int) (s : ItemData) : ItemData :=
  if s.2.1 = i then
    if s.1 = 0 then (0, j, 0, 0)
    else if s.1 = 1 then (1, j, d + s.2.2.1, 0)
    else (2, j, d + s.2.2.1, s.2.2.2)
  else s
def offset (i : Nat) (d : Int) (s : ItemData) : Int :=
  if s.2.1 = i then if s.1 = 0 then d else 0 else 0
def row (i j : Nat) (d : Int) (r : RowData) : RowData :=
  (r.1 + (r.2.map (fun a => a.1 * offset i d a.2)).sum,
    r.2.map (fun a => (a.1, item i j d a.2)))
def atom (i j : Nat) (d : Int) (a : AtomData) : AtomData :=
  (a.1, a.2.1, row i j d a.2.2)

/-- Literal all-code core translation in the unchanged radix-six grammar. -/
def core (i j : Nat) (d : Int) (code : Nat) : Nat :=
  if code % 6 = 0 then 0 else if code % 6 = 1 then 1
  else if code % 6 = 2 then
    6 * Encodable.encode (atom i j d
      ((Encodable.decode (code / 6) : Option AtomData).getD (0, 0, (0 : Int), []))) + 2
  else if code % 6 = 3 then 6 * core i j d (code / 6) + 3
  else 6 * Nat.pair (core i j d (code / 6).unpair.1)
    (core i j d (code / 6).unpair.2) + code % 6
termination_by code
decreasing_by
  all_goals
    have hpos : 0 < code := by omega
    have hd : code / 6 < code := Nat.div_lt_self hpos (by decide)
    have hl := Nat.unpair_left_le (code / 6)
    have hr := Nat.unpair_right_le (code / 6)
    omega

def conjunction (a b : Nat) : Nat := 6 * Nat.pair a b + 4
def disjunction (a b : Nat) : Nat := 6 * Nat.pair a b + 5
def negative (a : Nat) : Nat := 6 * a + 3
def anchorDomain (j : Nat) (d : Int) : Nat :=
  6 * Encodable.encode ((0, 0, d, [(1, (0, j, 0, 0))]) : AtomData) + 2
def substitute (i j : Nat) (d : Int) (code : Nat) : Nat :=
  disjunction (conjunction (anchorDomain j d) (core i j d code))
    (conjunction (negative (anchorDomain j d)) (BoundedRows.Code.formula i 0 code))
end Code

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SignedRows
