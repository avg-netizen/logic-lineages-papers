module
public import LogicLineages.OrdinalComparison.WWCanonicalPrimeDefinitions
public import Mathlib.Computability.Primrec.List
public import Lean.Elab.Tactic.Omega
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SyntaxCode

def arrowCode (a b : Nat) : Nat := Nat.pair a b + 1

def typeCode : Ty → Nat
  | .ground => 0
  | .arrow a b => arrowCode (typeCode a) (typeCode b)

/-- Every natural number is a genuine simple type code. -/
def decodeType : Nat → Ty
  | 0 => .ground
  | n+1 => .arrow (decodeType n.unpair.1) (decodeType n.unpair.2)
termination_by n => n
decreasing_by
  · exact Nat.lt_succ_of_le (Nat.unpair_left_le _)
  · exact Nat.lt_succ_of_le (Nat.unpair_right_le _)

def typeLevel : Nat → Nat
  | 0 => 0
  | n+1 => max (typeLevel n.unpair.1 + 1) (typeLevel n.unpair.2)
termination_by n => n
decreasing_by
  · exact Nat.lt_succ_of_le (Nat.unpair_left_le _)
  · exact Nat.lt_succ_of_le (Nat.unpair_right_le _)

def caseCode (a : Nat) : Nat := arrowCode 0 (arrowCode a (arrowCode a a))
def recCode (a : Nat) : Nat :=
  arrowCode 0 (arrowCode (arrowCode 0 (arrowCode a a)) (arrowCode a a))
end LogicLineages.OrdinalComparison.Source.SyntaxCode
