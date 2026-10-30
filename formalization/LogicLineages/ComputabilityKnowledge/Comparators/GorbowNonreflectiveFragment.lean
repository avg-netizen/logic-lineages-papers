module

public import LogicLineages.ComputabilityKnowledge.GorbowNonreflectiveFragment

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowNonreflectiveFragment
open GorbowSyntax GorbowSortedRevision GorbowSortedRevisionEventual
open LogicLineages.ComputabilityKnowledge.GorbowNonreflectiveFragment

def AxiomThreshold : Prop := ∀ (σ : Sentence), Axiom σ → ∀ initial,
  Threshold GorbowAtomicRegistry.ground initial σ 1

def FiniteBlockThreshold : Prop := ∀ initial (used : List Sentence) N (σ : Sentence),
  GorbowTheoryProof.Derivation (fun τ => Axiom τ ∨ τ ∈ used) σ →
  (∀ τ ∈ used, Threshold GorbowAtomicRegistry.ground initial τ N) →
  Threshold GorbowAtomicRegistry.ground initial σ (max 1 N)

def IndexedSoundness : Prop := ∀ N (σ : Sentence), Derives N σ → ∀ initial,
  Threshold GorbowAtomicRegistry.ground initial σ N

def ConcreteModel : Prop := ∀ N (σ : Sentence), Derives N σ →
  σ.realize (stage GorbowAtomicRegistry.ground GorbowKnowledgeDispatch.emptyInitial N) Fin.elim0

def FiniteCommonStage : Prop := ∀ (sentences : List Sentence),
  (∀ σ ∈ sentences, Provable σ) → ∃ N, ∀ initial σ, σ ∈ sentences →
    Threshold GorbowAtomicRegistry.ground initial σ N

def RuleClosure : Prop := ∀ σ : Sentence,
  (Provable σ → Provable (truthSentence σ)) ∧
  (Provable (truthSentence σ) → Provable σ) ∧
  (Provable σ → Provable (allAgentsKnow σ)) ∧
  (Provable (truthSentence σ) → Provable (allAgentsKnow σ))

def FragmentConsistency : Prop := ¬ Provable falseEquality

def Target : Prop := AxiomThreshold ∧ FiniteBlockThreshold ∧ IndexedSoundness ∧ ConcreteModel ∧
  FiniteCommonStage ∧ RuleClosure ∧ FragmentConsistency
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowNonreflectiveFragment
