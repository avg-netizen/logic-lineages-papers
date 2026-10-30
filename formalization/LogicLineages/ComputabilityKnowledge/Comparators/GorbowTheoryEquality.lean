module

public import LogicLineages.ComputabilityKnowledge.GorbowTheoryEquality

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowTheoryEquality
open GorbowSyntax GorbowTheoryProof GorbowStandardInstances GorbowClosedEquality

def FormulaImplication : Prop := ∀ (A : Sentence → Prop) (φ : Formula 1) (t u : Term 0),
  Derivation A (.equal t u) → Nonempty (Derivation A (.imp (instantiate φ t) (instantiate φ u)))

def Symmetry : Prop := ∀ (A : Sentence → Prop) (t u : Term 0),
  Derivation A (.equal t u) → Nonempty (Derivation A (.equal u t))

def Transitivity : Prop := ∀ (A : Sentence → Prop) (t u v : Term 0),
  Derivation A (.equal t u) → Derivation A (.equal u v) → Nonempty (Derivation A (.equal t v))

def TermCongruence : Prop := ∀ (A : Sentence → Prop) (f : Term 1) (t u : Term 0),
  Derivation A (.equal t u) → Nonempty (Derivation A (.equal (instantiateTerm f t) (instantiateTerm f u)))

def FormulaEquivalence : Prop := ∀ (A : Sentence → Prop) (φ : Formula 1) (t u : Term 0),
  Derivation A (.equal t u) → Nonempty (Derivation A
    (GorbowBooleanTruth.biconditional (instantiate φ t) (instantiate φ u)))

def Target : Prop := FormulaImplication ∧ Symmetry ∧ Transitivity ∧ TermCongruence ∧ FormulaEquivalence
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowTheoryEquality
