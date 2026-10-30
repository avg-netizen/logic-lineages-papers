module

public import LogicLineages.ComputabilityKnowledge.GorbowFormulaPrefixCode
public import Mathlib.Computability.Primrec.List

@[expose] public section

/-! Literal constructor programs and a numerical encoding of each syntax
sort. The two sorts are not asserted to have disjoint numeric ranges. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowCodeConstructors
open GorbowSyntax

def variableCode (i : Nat) : List Nat := [0,i]
def unary (tag : Nat) (raw : List Nat) : List Nat := tag :: raw
def binary (tag : Nat) (a b : List Nat) : List Nat := tag :: (a ++ b)
def numeral (k : Nat) : List Nat := List.replicate k 2 ++ [1]
def number (raw : List Nat) : Nat := Encodable.encode raw
def termNumber {n : Nat} (t : Term n) : Nat := number (GorbowTermPrefixCode.encode t)
def formulaNumber {n : Nat} (φ : Formula n) : Nat := number (GorbowFormulaPrefixCode.encode φ)
end LogicLineages.ComputabilityKnowledge.GorbowCodeConstructors
