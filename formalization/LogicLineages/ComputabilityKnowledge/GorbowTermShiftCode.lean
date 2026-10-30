module

public import LogicLineages.ComputabilityKnowledge.GorbowSyntaxValidation
public import LogicLineages.ComputabilityKnowledge.GorbowFormulaSubstitution

@[expose] public section

/-! Literal index shift for replacement terms, not a formula substitution.
Only tokens in the scanner's awaited-index state are changed. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowTermShiftCode
open GorbowSyntax GorbowSyntaxValidation

def shiftVar (n b : Nat) (i : Fin n) : Fin (n+b) :=
  ⟨i.val+b, Nat.add_lt_add_right i.isLt b⟩

def shiftTerm {n : Nat} (b : Nat) (t : Term n) : Term (n+b) :=
  GorbowFormulaSubstitution.renameTerm (shiftVar n b) t

abbrev OutputState := State × List Nat

def shiftedToken (b : Nat) (state : State) (token : Nat) : Nat :=
  match state with
  | some (task :: _) => if task.1 = 2 then token+b else token
  | _ => token

def shiftStep (b : Nat) (s : OutputState) (token : Nat) : OutputState :=
  (step s.1 token, s.2 ++ [shiftedToken b s.1 token])

def shiftRaw (n b : Nat) (raw : List Nat) : List Nat :=
  (raw.foldl (shiftStep b) (some [(0,n)],[])).2

def shiftCode (n b : Nat) (raw : List Nat) : Option (List Nat) :=
  if validTerm n raw then some (shiftRaw n b raw) else none
end LogicLineages.ComputabilityKnowledge.GorbowTermShiftCode
