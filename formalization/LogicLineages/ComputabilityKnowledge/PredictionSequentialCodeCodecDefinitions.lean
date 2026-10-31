module
public import Mathlib.Computability.TuringMachine.Config
public import Mathlib.Computability.Primrec.List
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionSequentialCodeCodec
abbrev Code := Turing.ToPartrec.Code

/-- Literal encoding of the actual Mathlib sequential programs. -/
def code : Code → Nat
  | .zero' => 0
  | .succ => 1
  | .tail => 2
  | .cons a b => 8 * Nat.pair (code a) (code b) + 3
  | .comp a b => 8 * Nat.pair (code a) (code b) + 4
  | .case a b => 8 * Nat.pair (code a) (code b) + 5
  | .fix a => 8 * Nat.pair (code a) 0 + 6

/-- Total decreasing numeric fold; malformed atomic tags are passed to `leaf`.
A fix node uses the left child and carries canonical right payload zero. -/
def fold {α : Type} (leaf : Nat → α) (branch : Nat → α → α → α) : Nat → α
  | n => if h : n % 8 < 3 ∨ n % 8 = 7 then leaf n else
    have hn : 0 < n := by omega
    have hd : n / 8 < n := Nat.div_lt_self hn (by decide)
    let p := (n / 8).unpair
    have hl : p.1 < n := (Nat.unpair_left_le _).trans_lt hd
    have hr : p.2 < n := (Nat.unpair_right_le _).trans_lt hd
    branch (n % 8) (fold leaf branch p.1) (fold leaf branch p.2)
termination_by n => n
decreasing_by all_goals assumption

def termFold {α : Type} (leaf : Nat → α) (branch : Nat → α → α → α) : Code → α
  | .zero' => leaf 0
  | .succ => leaf 1
  | .tail => leaf 2
  | .cons a b => branch 3 (termFold leaf branch a) (termFold leaf branch b)
  | .comp a b => branch 4 (termFold leaf branch a) (termFold leaf branch b)
  | .case a b => branch 5 (termFold leaf branch a) (termFold leaf branch b)
  | .fix a => branch 6 (termFold leaf branch a) (leaf 0)

def leafCode (n : Nat) : Code := if n = 1 then .succ else if n = 2 then .tail else .zero'
def branchCode (n : Nat) (a b : Code) : Code :=
  if n = 3 then .cons a b else if n = 4 then .comp a b else if n = 5 then .case a b else .fix a
/-- Total decoding with deterministic fallback for malformed words. -/
def decode : Nat → Code := fold leafCode branchCode
/-- Canonical numeric image, defined independently of any `Primcodable` instance. -/
def normalize (n : Nat) : Nat := code (decode n)
end LogicLineages.ComputabilityKnowledge.PredictionSequentialCodeCodec
