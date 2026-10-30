module

public import LogicLineages.ComputabilityKnowledge.GorbowStandardInstances

@[expose] public section

/-! One explicit arithmetic-term-expressible tuple convention for the source's
U/u multiplexing. It is distinct from the already fixed formulaNumber/termNumber
encoding, which this module does not alter. No decoding or represented graph
of a syntax registry is claimed here. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowRegistryTuple
open GorbowSyntax

def pair (a b : Nat) : Nat := (a+b)*(a+b)+a

def tuple : List Nat → Nat
  | [] => 0
  | a::as => pair a (tuple as)+1

def header (arity tag : Nat) (args : List Nat) : Nat := pair arity (pair tag (tuple args))

def pairTerm {n : Nat} (a b : Term n) : Term n := .add (.mul (.add a b) (.add a b)) a

def tupleTerm {n : Nat} : List (Term n) → Term n
  | [] => .zero
  | a::as => .succ (pairTerm a (tupleTerm as))

def headerTerm {n : Nat} (arity tag : Nat) (args : List (Term n)) : Term n :=
  pairTerm (Term.numeral arity) (pairTerm (Term.numeral tag) (tupleTerm args))
end LogicLineages.ComputabilityKnowledge.GorbowRegistryTuple
