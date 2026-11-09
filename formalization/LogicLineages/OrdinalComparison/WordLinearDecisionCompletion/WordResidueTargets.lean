module
public import LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.WordResidueDefinitions
public import Mathlib.Data.Int.ModEq

@[expose] public section
namespace LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.WordResidue.Targets
open PolynomialGraphCompletion

def LiteralLetterResidue : Prop := ∀ D m : Nat, 0 < m → ∀ a : Letter,
  LetterAllowed D a → ∀ t : Nat, letterTail m a ≤ t →
    LetterDomain a t ∧ Int.ModEq (m : Int) (letterValue a t : Int)
      ((letterAffine m a).1 * (t : Int) + (letterAffine m a).2)

def LiteralWordResidue : Prop := ∀ D m : Nat, 0 < m → ∀ w : Word,
  WordAllowed D w → ∀ t : Nat, tail m w ≤ t →
    WordDomain w t ∧ Int.ModEq (m : Int) (wordValue w t : Int)
      ((affine m w).1 * (t : Int) + (affine m w).2)

def ExactSlope : Prop := ∀ m : Nat, ∀ w : Word,
  (affine m w).1 = if w.all (fun a => a.1 == 0) then 1 else 0

def LiteralShiftResidue : Prop := ∀ m : Nat, ∀ w : Word,
  (∀ a ∈ w, a.1 = 0) →
    affine m w = (1, (w.map (fun a => a.2.2.2)).sum)

def ActualRowResidue : Prop := ∀ D m : Nat, 0 < m → ∀ r : Row,
  RowAllowed D r → ∀ ν : Nat → Nat,
  (∀ i ∈ rowVariables r, rowTail m r ≤ ν i) →
    RowDomain r ν ∧ Int.ModEq (m : Int) (RowValue r ν) (RowValue (row m r) ν)

def ActualDivisibility : Prop := ∀ D m : Nat, ∀ r : Row,
  RowAllowed D r → ∀ ν : Nat → Nat,
  (∀ i ∈ rowVariables r, rowTail (m+1) r ≤ ν i) →
    (((m+1 : Nat) : Int) ∣ RowValue r ν ↔ ((m+1 : Nat) : Int) ∣ RowValue (row (m+1) r) ν)

def LiteralRawSyntax : Prop := ∀ m : Nat, ∀ r : Row,
  (row m r).2 = r.2.map (fun a => (a.1 * (affine m a.2.2).1, (a.2.1, []))) ∧
  (∀ a ∈ (row m r).2, a.2.2 = [])

def ExactNames : Prop := ∀ m : Nat, ∀ r : Row,
  rowVariables (row m r) = rowVariables r

def OutputDomainsAndDegree : Prop := ∀ D m : Nat, ∀ r : Row, ∀ ν : Nat → Nat,
  RowDomain (row m r) ν ∧ RowAllowed D (row m r)

def LetterPrograms : Prop :=
  Primrec (fun p : Nat × Letter => letterAffine p.1 p.2) ∧
  Primrec (fun p : Nat × Letter => letterTail p.1 p.2)

def WordPrograms : Prop :=
  Primrec (fun p : Nat × Word => affine p.1 p.2) ∧
  Primrec (fun p : Nat × Word => tail p.1 p.2)

def RowPrograms : Prop :=
  Primrec (fun p : Nat × Row => row p.1 p.2) ∧
  Primrec (fun p : Nat × Row => rowTail p.1 p.2)

end LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.WordResidue.Targets
