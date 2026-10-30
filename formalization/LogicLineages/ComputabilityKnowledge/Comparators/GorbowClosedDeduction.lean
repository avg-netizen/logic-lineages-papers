module

public import LogicLineages.ComputabilityKnowledge.GorbowClosedDeduction

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowClosedDeduction
open GorbowSyntax GorbowTheoryProof
open LogicLineages.ComputabilityKnowledge.GorbowClosedDeduction

def ClosedSyntax : Prop :=
  (∀ (R : Sentence), weakenClosed 0 R = R) ∧
  (∀ n (R : Sentence), GorbowPACore.weaken (weakenClosed n R) = weakenClosed (n+1) R)

def Deduction : Prop := ∀ (A : Sentence → Prop) (R : Sentence) n (φ : Formula n),
  Derivation (extend A R) φ → Nonempty (Derivation A (.imp (weakenClosed n R) φ))

def Discharge : Prop := ∀ (A : Sentence → Prop) (R : Sentence) n (φ : Formula n),
  Derivation A (.imp (weakenClosed n R) φ) → Nonempty (Derivation (extend A R) φ)

def ExactExtension : Prop := ∀ (A : Sentence → Prop) (R : Sentence) n (φ : Formula n),
  Nonempty (Derivation (extend A R) φ) ↔ Nonempty (Derivation A (.imp (weakenClosed n R) φ))

def ClosedExtension : Prop := ∀ (A : Sentence → Prop) (R σ : Sentence),
  Nonempty (Derivation (extend A R) σ) ↔ Nonempty (Derivation A (.imp R σ))

def Target : Prop := ClosedSyntax ∧ Deduction ∧ Discharge ∧ ExactExtension ∧ ClosedExtension
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowClosedDeduction
