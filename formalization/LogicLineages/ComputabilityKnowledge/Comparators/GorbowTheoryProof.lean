module

public import LogicLineages.ComputabilityKnowledge.GorbowTheoryProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowTheoryProof
open GorbowSyntax
open LogicLineages.ComputabilityKnowledge.GorbowTheoryProof

def WeakeningSemantics : Prop := ∀ n (σ : Sentence) I v,
  (weakenClosed n σ).realize I v ↔ σ.realize I Fin.elim0

def UsedMembership : Prop := ∀ (A : Sentence → Prop) n (φ : Formula n) (p : Derivation A φ),
  ∀ σ ∈ usedAxioms p, A σ

def Rebase : Prop := ∀ (A B : Sentence → Prop) n (φ : Formula n) (p : Derivation A φ),
  (∀ σ ∈ usedAxioms p, B σ) → Nonempty (Derivation B φ)

def Monotonicity : Prop := ∀ (A B : Sentence → Prop), (∀ σ, A σ → B σ) →
  ∀ n (φ : Formula n), Nonempty (Derivation A φ) → Nonempty (Derivation B φ)

def FiniteRestriction : Prop := ∀ (A : Sentence → Prop) n (φ : Formula n) (p : Derivation A φ),
  Nonempty (Derivation (fun σ => σ∈usedAxioms p) φ)

def CoreEmbedding : Prop := ∀ (A : Sentence → Prop) n (φ : Formula n),
  GorbowPACore.Proof φ → Nonempty (Derivation A φ)

def FiniteUseSoundness : Prop := ∀ (A : Sentence → Prop) n (φ : Formula n) (p : Derivation A φ) I,
  (∀ σ ∈ usedAxioms p, σ.realize I Fin.elim0) → ∀ v, φ.realize I v

def TheorySoundness : Prop := ∀ (A : Sentence → Prop) n (φ : Formula n) (p : Derivation A φ) I,
  (∀ σ, A σ → σ.realize I Fin.elim0) → ∀ v, φ.realize I v

def Target : Prop := WeakeningSemantics ∧ UsedMembership ∧ Rebase ∧ Monotonicity ∧
  FiniteRestriction ∧ CoreEmbedding ∧ FiniteUseSoundness ∧ TheorySoundness
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowTheoryProof
