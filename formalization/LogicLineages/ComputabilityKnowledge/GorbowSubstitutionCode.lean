module

public import LogicLineages.ComputabilityKnowledge.GorbowLiftedDictionary

@[expose] public section

/-! Literal simultaneous substitution scanner. Formula equality tag0 is not
a term-variable tag: the pending task kind distinguishes them. Under binders
only bound indices are preserved, while actual free replacements are shifted.
Validity guards demand exactly n well-typed replacement codes in ambient m. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowSubstitutionCode
open GorbowSyntax GorbowSyntaxValidation GorbowLiftedDictionary
abbrev OutputState := State × List Nat

def emit (n m : Nat) (dict : List (List Nat)) (state : State) (token : Nat) : List Nat :=
  match state with
  | some (task :: _) =>
      if task.1 = 2 then liftedCode m (task.2-n) dict token
      else if task.1 = 0 ∧ token = 0 then [] else [token]
  | _ => [token]

def subStep (n m : Nat) (dict : List (List Nat)) (s : OutputState) (token : Nat) : OutputState :=
  (step s.1 token, s.2 ++ emit n m dict s.1 token)

def subRaw (kind n m : Nat) (dict : List (List Nat)) (raw : List Nat) : List Nat :=
  (raw.foldl (subStep n m dict) (some [(kind,n)],[])).2

def substituteTermCode (n m : Nat) (dict : List (List Nat)) (raw : List Nat) : Option (List Nat) :=
  if validTerm n raw && dictionaryValid n m dict then some (subRaw 0 n m dict raw) else none

def substituteFormulaCode (n m : Nat) (dict : List (List Nat)) (raw : List Nat) : Option (List Nat) :=
  if validFormula n raw && dictionaryValid n m dict then some (subRaw 1 n m dict raw) else none
end LogicLineages.ComputabilityKnowledge.GorbowSubstitutionCode
