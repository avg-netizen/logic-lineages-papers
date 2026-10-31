module

public import Mathlib.Computability.TuringMachine.PostTuringMachine

@[expose] public section
/-! Literal finite-control input-tape code evaders, with blank distinct from
both input bits. No universal-numbering or evaln simulation is assumed.
The output is written at the final head; the suffix beyond that cell survives. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeMachine
open Turing

inductive State (k : Nat)
  | scan : Fin (k + 1) → State k
  | done : Bool → State k
  deriving DecidableEq

instance (k : Nat) : Inhabited (State k) := ⟨.scan ⟨k, Nat.lt_succ_self k⟩⟩

abbrev Symbol := Option Bool
abbrev Cfg (k : Nat) := TM0.Cfg Symbol (State k)

def machine (k : Nat) : TM0.Machine Symbol (State k)
  | .done _, _ => none
  | .scan i, a =>
    if i.val = 0 then some (.done false, .write (some false))
    else if a = none then some (.done true, .write (some true))
    else some (.scan ⟨i.val - 1, (Nat.sub_le i.val 1).trans_lt i.isLt⟩, .move .right)

def step (k : Nat) : Cfg k → Option (Cfg k) := TM0.step (machine k)

def initial (k : Nat) (xs : List Bool) : Cfg k := TM0.init (xs.map some)

inductive Run (k : Nat) : Cfg k → Cfg k → Nat → Prop
  | refl (c : Cfg k) : Run k c c 0
  | next {c c' d : Cfg k} {n : Nat} :
      step k c = some c' → Run k c' d n → Run k c d (n + 1)

/-- Successful transitions plus the final halting observation, each charged
one unit. Input construction is not charged as a mandatory full-input scan. -/
def HaltsWith (k : Nat) (xs : List Bool) (bit : Bool) (time : Nat) : Prop :=
  ∃ (d : Cfg k) (n : Nat), Run k (initial k xs) d n ∧
    step k d = none ∧ d.q = .done bit ∧ d.Tape.head = some bit ∧ time = n + 1

end LogicLineages.ComputabilityKnowledge.PredictionTapeMachine
