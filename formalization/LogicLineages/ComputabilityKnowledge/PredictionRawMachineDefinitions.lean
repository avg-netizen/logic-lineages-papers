module

public import Mathlib.Computability.TuringMachine.StackTuringMachine

@[expose] public section
/-! A finite-control raw TM2 code evader. Actual terminal configurations retain
unread input. TM2 transitions and primitive input inspections are distinguished;
no ordinary-code numbering or tape-runtime simulation is asserted. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionRawMachine

abbrev Alphabet (_ : Bool) := Bool
abbrev Label (k : Nat) := Fin (k + 1)
abbrev Cfg (k : Nat) := Turing.TM2.Cfg Alphabet (Label k) Bool
abbrev Stmt (k : Nat) := Turing.TM2.Stmt Alphabet (Label k) Bool

def predecessor {k : Nat} (i : Label k) : Label k :=
  ⟨i.val - 1, (Nat.sub_le i.val 1).trans_lt i.isLt⟩

def evaderStmt (k : Nat) (i : Label k) : Stmt k :=
  if i.val = 0 then
    .push true (fun _ => false) .halt
  else
    .pop false (fun _ a => a.isSome)
      (.branch id (.goto fun _ => predecessor i)
        (.push true (fun _ => true) .halt))

def runningCfg (k : Nat) (i : Label k) (state : Bool) (input output : List Bool) : Cfg k :=
  ⟨some i, state, fun b => if b then output else input⟩

def terminalCfg (k : Nat) (state : Bool) (input output : List Bool) : Cfg k :=
  ⟨none, state, fun b => if b then output else input⟩

def initialCfg (k : Nat) (input : List Bool) : Cfg k :=
  runningCfg k ⟨k, Nat.lt_succ_self k⟩ false input []

def machineStep (k : Nat) : Cfg k → Option (Cfg k) := Turing.TM2.step (evaderStmt k)

end LogicLineages.ComputabilityKnowledge.PredictionRawMachine
