module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.Definitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.Specialization
open PolynomialCircuit

/-- Remove the first parameter and shift every remaining variable down once.
Repeated occurrences remain repeated, so powers are preserved literally. -/
def dropParameter : List Nat → List Nat
  | [] => []
  | 0 :: vs => dropParameter vs
  | (i + 1) :: vs => i :: dropParameter vs

def term (x : Nat) (m : Monomial) : Monomial :=
  (m.1 * (x : Int) ^ m.2.count 0,dropParameter m.2)

def specialize (x : Nat) (p : Code) : Code :=
  ⟨p.inputCount - 1,p.monomials.map (term x)⟩

/-- Explicit canonical output encoding. A negative coefficient scaled to
zero must use the ordinary zero tag, not a negative-zero representation. -/
def rawTerm (x : Nat) : Monomial → List Nat
  | (.ofNat k,vs) =>
      0 :: (k * x ^ vs.count 0) :: (dropParameter vs).length :: dropParameter vs
  | (.negSucc k,vs) =>
      let mag := (k + 1) * x ^ vs.count 0
      if mag = 0 then 0 :: 0 :: (dropParameter vs).length :: dropParameter vs
      else 1 :: (mag - 1) :: (dropParameter vs).length :: dropParameter vs

def rawTerms (x : Nat) : Monomials → List Nat
  | [] => []
  | m :: ms => rawTerm x m ++ rawTerms x ms

/-- This is an actual natural-number function once the finite input code p
is fixed. It does not inspect or extract a code from a Diophantine proof. -/
def specializationCode (p : Code) (x : Nat) : Nat :=
  Encodable.encode ((p.inputCount - 1) :: rawTerms x p.monomials)

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.Specialization
