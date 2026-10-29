module

public import LogicLineages.ComputabilityKnowledge.CircuitComparison
public import Mathlib.Computability.Partrec

@[expose] public section

/-! Exact finite-fragment counterexample search, paper02 lines232–236.
Uses the existing prefix Expr codec and framed comparison codec unchanged.
Tokenization distinguishes variable payloads from operator tags. Both syntax
and numeric stacks reject malformed expressions and out-of-bound variables.
The semantic counterexample predicates quantify literal source terms and
finite positive valuations; they are not defined as success of this search. -/
namespace LogicLineages.ComputabilityKnowledge.FiniteComparisonEnumeration

open PositiveExpression CircuitReduction
abbrev Token := Nat × Nat

def tokenize : List Nat → Option (List Token)
  | [] => some []
  | 0 :: rest => (tokenize rest).map ((0,0) :: ·)
  | 1 :: i :: rest => (tokenize rest).map ((1,i) :: ·)
  | 2 :: rest => (tokenize rest).map ((2,0) :: ·)
  | 3 :: rest => (tokenize rest).map ((3,0) :: ·)
  | _ => none

def syntaxStep (d : Nat) (t : Token) (stack : List (Expr Nat)) : Option (List (Expr Nat)) :=
  match t.1 with
  | 0 => some (.one :: stack)
  | 1 => if t.2 < d then some (.var t.2 :: stack) else none
  | 2 => match stack with | a :: b :: rest => some (.add a b :: rest) | _ => none
  | 3 => match stack with | a :: b :: rest => some (.emul a b :: rest) | _ => none
  | _ => none

def syntaxStack (d : Nat) (ts : List Token) : Option (List (Expr Nat)) :=
  ts.foldr (fun t result => result.bind (syntaxStep d t)) (some [])

def decodeExpr (d : Nat) (code : List Nat) : Option (Expr Nat) := do
  let ts ← tokenize code
  let stack ← syntaxStack d ts
  match stack with | [e] => some e | _ => none

def tupleValue (values : List Nat) : Nat → PosNat :=
  fun i => ⟨values.getD i 0 + 1,Nat.zero_lt_succ _⟩

def tupleOf (d : Nat) (values : List Nat) : Fin d → PosNat := fun i => tupleValue values i.val

def numericStep (d : Nat) (values : List Nat) (t : Token) (stack : List Nat) : Option (List Nat) :=
  match t.1 with
  | 0 => some (1 :: stack)
  | 1 => if t.2 < d then some ((tupleValue values t.2).val :: stack) else none
  | 2 => match stack with | a :: b :: rest => some ((a+b) :: rest) | _ => none
  | 3 => match stack with | a :: b :: rest => some ((2^a*b) :: rest) | _ => none
  | _ => none

def numericStack (d : Nat) (values : List Nat) (ts : List Token) : Option (List Nat) :=
  ts.foldr (fun t result => result.bind (numericStep d values t)) (some [])

def evalCode (d : Nat) (code values : List Nat) : Option Nat := do
  let ts ← tokenize code
  let stack ← numericStack d values ts
  match stack with | [n] => some n | _ => none

def decodePair : List Nat → Option (Nat × Expr Nat × Expr Nat)
  | d :: na :: nb :: rest =>
    if rest.length = na+nb then do
      let a ← decodeExpr d (rest.take na)
      let b ← decodeExpr d (rest.drop na)
      pure (d,a,b)
    else none
  | _ => none

def evalPair (code values : List Nat) : Option (Nat × Nat) :=
  match code with
  | d :: na :: nb :: rest =>
    if rest.length = na+nb then do
      let a ← evalCode d (rest.take na) values
      let b ← evalCode d (rest.drop na) values
      pure (a,b)
    else none
  | _ => none

def enumValues (k : Nat) : List Nat := (Encodable.decode (α := List Nat) k).getD []
def enumTuple (d k : Nat) : Fin d → PosNat := tupleOf d (enumValues k)

def checkStrict (code : List Nat) (k : Nat) : Bool :=
  match evalPair code (enumValues k) with
  | some (a,b) => decide (¬ a < b)
  | none => false

def checkWeak (code : List Nat) (k : Nat) : Bool :=
  match evalPair code (enumValues k) with
  | some (a,b) => decide (¬ a ≤ b)
  | none => false

def StrictCounterexample (code : List Nat) : Prop :=
  ∃ (d : Nat) (a b : Expr Nat), code = CircuitComparison.encodeComparison (d,a,b) ∧
    Bounded d a ∧ Bounded d b ∧ ∃ ρ : Fin d → PosNat,
      ¬ a.eval (CircuitComparison.finiteVal ρ) < b.eval (CircuitComparison.finiteVal ρ)

def WeakCounterexample (code : List Nat) : Prop :=
  ∃ (d : Nat) (a b : Expr Nat), code = CircuitComparison.encodeComparison (d,a,b) ∧
    Bounded d a ∧ Bounded d b ∧ ∃ ρ : Fin d → PosNat,
      ¬ a.eval (CircuitComparison.finiteVal ρ) ≤ b.eval (CircuitComparison.finiteVal ρ)

end LogicLineages.ComputabilityKnowledge.FiniteComparisonEnumeration
