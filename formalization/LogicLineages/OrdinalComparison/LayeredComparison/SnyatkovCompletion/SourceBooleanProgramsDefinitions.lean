module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceBooleanGraphDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainFrontierProgramsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceBooleanPrograms
open NormalForm

def shiftSummand (d : Nat) : Summand → Summand
  | .variable i => .variable (d + i)
  | .phi i e => .phi (d + i) e
  | .hyperPhi i e h => .hyperPhi (d + i) e h

def shiftRow (d : Nat) (r : Row) : Row :=
  (r.1, r.2.map (fun a => (a.1, shiftSummand d a.2)))
def shiftAtom (d : Nat) : Atom → Atom
  | .nonnegative r => .nonnegative (shiftRow d r)
  | .divisible m r => .divisible m (shiftRow d r)
def shift (d : Nat) : Formula → Formula
  | .truth => .truth
  | .falsity => .falsity
  | .atom a => .atom (shiftAtom d a)
  | .negative p => .negative (shift d p)
  | .conjunction p q => .conjunction (shift d p) (shift d q)
  | .disjunction p q => .disjunction (shift d p) (shift d q)

namespace Code
def shiftItem (d : Nat) (a : NormalForm.Code.ItemData) : NormalForm.Code.ItemData :=
  (a.1, d + a.2.1, a.2.2.1, a.2.2.2)
def shiftRow (d : Nat) (r : NormalForm.Code.RowData) : NormalForm.Code.RowData :=
  (r.1, r.2.map (fun a => (a.1, shiftItem d a.2)))
def shiftAtom (d : Nat) (a : NormalForm.Code.AtomData) : NormalForm.Code.AtomData :=
  (a.1, a.2.1, shiftRow d a.2.2)
def shift (d code : Nat) : Nat :=
  LinearRows.Code.mapAtoms (fun a => Encodable.encode (shiftAtom d (LinearRows.Code.decodeAtom a))) code

def count (term : Nat) : Nat := (SourceTermGraph.Code.instructions term).length
abbrev Payload := Bool × (Nat × Nat)
/-- Literal test, joined term code, and relative Boolean predicate code. -/
def payload (code : Nat) : Payload :=
  if code % 5 = 0 ∨ code % 5 = 1 then
    let a := (code / 5).unpair.1
    let b := (code / 5).unpair.2
    (true, 4 * Nat.pair a b + 2,
      SourceRows.Code.relation (code % 5 == 1) (count a - 1) (count a + count b - 1))
  else if code % 5 = 2 then
    let p := payload (code / 5)
    (p.1, p.2.1, 6 * p.2.2 + 3)
  else if code % 5 = 3 then
    let p := payload (code / 5).unpair.1
    let q := payload (code / 5).unpair.2
    (p.1 && q.1, 4 * Nat.pair p.2.1 q.2.1 + 2,
      6 * Nat.pair p.2.2 (shift (count p.2.1) q.2.2) + 4)
  else
    (false, (payload (code / 5).unpair.2).2.1, 1)
termination_by code
decreasing_by
  all_goals
    have hpos : 0 < code := by omega
    have hd : code / 5 < code := Nat.div_lt_self hpos (by decide)
    have hl := Nat.unpair_left_le (code / 5)
    have hr := Nat.unpair_right_le (code / 5)
    omega

def test (code : Nat) : Bool := (payload code).1
def forest (code : Nat) : Nat := (payload code).2.1
def predicate (code : Nat) : Nat := (payload code).2.2
def start (code : Nat) : Nat := SourceRows.Code.bound (SourceTermGraph.Code.instructions (forest code))
def graph (code : Nat) : Nat :=
  SourceTermGraph.Code.equations
    (SourceTermGraph.Code.run (SourceTermGraph.Code.instructions (forest code)) (start code, [], [])).2.2

def compile (code : Nat) : Nat :=
  SourceTermGraph.Code.conjunction (graph code) (shift (start code) (predicate code))
def decideExists (code : Nat) : Option Bool :=
  if test code then some (PlainFrontierPrograms.Code.answer (compile code)) else none
def decideForall (code : Nat) : Option Bool :=
  (decideExists (5 * code + 2)).map Bool.not
end Code

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceBooleanPrograms
