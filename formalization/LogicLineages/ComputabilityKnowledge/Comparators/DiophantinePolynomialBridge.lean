module

public import LogicLineages.ComputabilityKnowledge.DiophantinePolynomialBridge

@[expose] public section

/-! Independent supplier bridge target. No finite-auxiliary-type premise and
no effective extraction claim. The final power graph uses natural inputs,
including zero, and a genuine well-formed existing polynomial code. -/
namespace LogicLineages.ComputabilityKnowledge.Comparators.DiophantinePolynomialBridge

open PolynomialCircuit
open LogicLineages.ComputabilityKnowledge.DiophantinePolynomialBridge

/-- The genuine Mathlib predicate, not a new syntactic replacement. -/
def PolynomialCorrespondence : Prop :=
  ∀ (α : Type) (f : (α → Nat) → Int),
    IsPoly f ↔ ∃ P : MvPolynomial α Int,
      ∀ ν, MvPolynomial.eval (fun i => (ν i : Int)) P = f ν

/-- Quantifies the unmodified Mathlib `Dioph`, whose auxiliary type need not be finite. -/
def FiniteWitnessExtraction : Prop :=
  ∀ (n : Nat) (S : Set (Fin n → Nat)), Dioph S ↔ FiniteDiophantine S

/-- First n input variables and next m witnesses are shared literally. -/
def FramingFaithful : Prop :=
  ∀ (n m : Nat) (ν : Fin n → Nat) (w : Fin m → Nat),
    (∀ i : Fin n, joinedNat ν w i.val = ν i) ∧
    (∀ j : Fin m, joinedNat ν w (n+j.val) = w j) ∧
    Function.Injective (sumIndex n m) ∧
    (∀ i, sumIndex n m i < n+m)

/-- Coverage and evaluation are both explicit; arity zero is included. -/
def CodeCoverage : Prop :=
  ∀ (n m : Nat) (P : MvPolynomial (Fin n ⊕ Fin m) Int),
    ∃ p : Code, p.inputCount = n+m ∧ p.WellFormed ∧
      interpret p = MvPolynomial.rename (sumIndex n m) P ∧
      ∀ (ν : Fin n → Nat) (w : Fin m → Nat),
        MvPolynomial.eval (fun i => (joinedNat ν w i : Int)) (interpret p) =
          MvPolynomial.eval (fun i => ((Sum.elim ν w i : Nat) : Int)) P

def DiophantineCodeRepresentation : Prop :=
  ∀ (n : Nat) (S : Set (Fin n → Nat)),
    Dioph S ↔ ∃ (m : Nat) (p : Code), CodeRepresents S m p

def PowerGraphRepresentation : Prop :=
  ∃ (m : Nat) (p : Code), CodeRepresents powerGraph m p

def Target : Prop := PolynomialCorrespondence ∧ FiniteWitnessExtraction ∧
  FramingFaithful ∧ CodeCoverage ∧ DiophantineCodeRepresentation ∧ PowerGraphRepresentation

end LogicLineages.ComputabilityKnowledge.Comparators.DiophantinePolynomialBridge
