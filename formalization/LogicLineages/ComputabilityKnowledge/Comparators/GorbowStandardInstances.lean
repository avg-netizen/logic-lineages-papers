module

public import LogicLineages.ComputabilityKnowledge.GorbowStandardInstances

@[expose] public section

/-! Exact standard-N instance suppliers for paper12's quantifier/revision
argument. Interpretation is the original full-language syntax semantics;
there is no theorem/provability oracle or consistency conclusion here. -/
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowStandardInstances

open GorbowSyntax
open LogicLineages.ComputabilityKnowledge.GorbowStandardInstances

def LiteralInstantiation : Prop :=
  ∀ (n : Nat) (φ : Formula (n + 1)) (t : Term n) (I : Interpretation) (v : Fin n → Nat),
    (instantiate φ t).realize I v ↔ φ.realize I (Fin.cases (t.realize I v) v)

def ClosedTermInterpretation : Prop :=
  ∀ (n : Nat) (t : Term 0) (I : Interpretation) (v : Fin n → Nat),
    (closedTermInContext n t).realize I v = t.realize I Fin.elim0

def NumeralInstances : Prop :=
  ∀ (n : Nat) (φ : Formula (n + 1)) (k : Nat) (I : Interpretation) (v : Fin n → Nat),
    (instantiate φ (Term.numeral k)).realize I v ↔ φ.realize I (Fin.cases k v)

def FullClosedTermQuantifiers : Prop :=
  ∀ (n : Nat) (φ : Formula (n + 1)) (I : Interpretation) (v : Fin n → Nat),
    ((Formula.all φ).realize I v ↔
      ∀ t : Term 0, (instantiate φ (closedTermInContext n t)).realize I v) ∧
    ((Formula.ex φ).realize I v ↔
      ∃ t : Term 0, (instantiate φ (closedTermInContext n t)).realize I v)

def ArithmeticNumerals : Prop :=
  ∀ (n k : Nat), ArithmeticTerm (Term.numeral k : Term n)

def ArithmeticClosedTermQuantifiers : Prop :=
  ∀ (n : Nat) (φ : Formula (n + 1)) (I : Interpretation) (v : Fin n → Nat),
    ((Formula.all φ).realize I v ↔
      ∀ t : Term 0, ArithmeticTerm t → (instantiate φ (closedTermInContext n t)).realize I v) ∧
    ((Formula.ex φ).realize I v ↔
      ∃ t : Term 0, ArithmeticTerm t ∧ (instantiate φ (closedTermInContext n t)).realize I v)

def Target : Prop := LiteralInstantiation ∧ ClosedTermInterpretation ∧ NumeralInstances ∧
  FullClosedTermQuantifiers ∧ ArithmeticNumerals ∧ ArithmeticClosedTermQuantifiers

end LogicLineages.ComputabilityKnowledge.Comparators.GorbowStandardInstances
