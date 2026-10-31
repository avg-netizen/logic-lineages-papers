module

public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Computability.Primrec.List

@[expose] public section
/-! Effective finite transition tables and a literal bounded tape simulator.
Every natural number decodes, with malformed encodings defaulting to the
empty halting table. No acceptability/universality claim is made here. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeTable
open Turing

abbrev Symbol := Option Bool
/-- `inl false/true` move left/right; `inr a` writes a. -/
abbrev Action := Bool ⊕ Symbol
abbrev Table := Nat × List (Option (Nat × Action))
abbrev Raw := Nat × Symbol × List Symbol × List Symbol

def decodeTable (code : Nat) : Table := (Encodable.decode (α := Table) code).getD (0, [])

def symbolIndex : Symbol → Nat
  | none => 0
  | some false => 1
  | some true => 2

def lookup (p : Table) (q : Nat) (a : Symbol) : Option (Nat × Action) :=
  (p.2[q * 3 + symbolIndex a]?).bind id

def actionStmt : Action → TM0.Stmt Symbol
  | .inl false => .move .left
  | .inl true => .move .right
  | .inr a => .write a

def machine (p : Table) : TM0.Machine Symbol Nat :=
  fun q a => (lookup p q a).map (fun x => (x.1, actionStmt x.2))

def execute (q : Nat) (a : Action) (c : Raw) : Raw :=
  match a with
  | .inl false => (q, c.2.2.1.headI, c.2.2.1.tail, c.2.1 :: c.2.2.2)
  | .inl true => (q, c.2.2.2.headI, c.2.1 :: c.2.2.1, c.2.2.2.tail)
  | .inr b => (q, b, c.2.2.1, c.2.2.2)

def step (p : Table) (c : Raw) : Option Raw :=
  (lookup p c.1 c.2.1).map (fun x => execute x.1 x.2 c)

def toCfg (c : Raw) : TM0.Cfg Symbol Nat :=
  ⟨c.1, ⟨c.2.1, ListBlank.mk c.2.2.1, ListBlank.mk c.2.2.2⟩⟩

def initial (p : Table) (xs : List Bool) : Raw :=
  (p.1, (xs.map some).headI, [], (xs.map some).tail)

/-- The fuel counts attempted transitions, including the terminating halt
observation. Returning none only means the finite simulation timed out. -/
def bounded (p : Table) : Nat → Raw → Option Raw
  | 0, _ => none
  | n + 1, c => match step p c with
    | none => some c
    | some c' => bounded p n c'

inductive Run (p : Table) : Raw → Raw → Nat → Prop
  | refl (c : Raw) : Run p c c 0
  | next {c c' d : Raw} {n : Nat} :
      step p c = some c' → Run p c' d n → Run p c d (n + 1)

def simulate (code fuel : Nat) (xs : List Bool) : Option Raw :=
  bounded (decodeTable code) fuel (initial (decodeTable code) xs)

end LogicLineages.ComputabilityKnowledge.PredictionTapeTable
