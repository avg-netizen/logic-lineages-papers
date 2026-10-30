module

public import LogicLineages.ComputabilityKnowledge.GorbowAtomicTruth
public import LogicLineages.ComputabilityKnowledge.GorbowKnowledgeDispatch
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryProof
public import LogicLineages.ComputabilityKnowledge.GorbowSortedRevisionEventual

@[expose] public section
/-! An explicitly named nonreflective fragment: the literal FS schemas,
knowledge bridge/nontriviality/veracity/distribution and arithmetic Barcan.
It omits Base defining axioms and reflection. The indices below are syntactic
proof-budget annotations, not semantic assumptions. No full KT/DCB or source
consistency theorem is asserted. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowNonreflectiveFragment
open GorbowSyntax GorbowSortedRevision GorbowSortedRevisionEventual

inductive Axiom : Sentence → Prop
  | negation : Axiom GorbowBooleanTruth.negAxiom
  | implication : Axiom GorbowBooleanTruth.impAxiom
  | conjunction : Axiom GorbowBooleanTruth.conjAxiom
  | disjunction : Axiom GorbowBooleanTruth.disjAxiom
  | universal : Axiom GorbowSortedQuantifierTruth.forallAxiom
  | existential : Axiom GorbowSortedQuantifierTruth.existsAxiom
  | barcan : Axiom GorbowSortedQuantifierTruth.barcanAxiom
  | atomic {n m} (R : Formula m) (names : Fin n → Fin m) :
      GorbowRevisionComposition.AtomicMinus R → Function.Injective names →
      GorbowNameDictionary.Covers R names → Axiom (GorbowAtomicTruth.atomicAxiom R names)
  | nontriviality : Axiom GorbowSortedKnowledgeAxioms.nontriviality
  | bridge : Axiom GorbowSortedKnowledgeAxioms.bridge
  | veracity : Axiom GorbowSortedKnowledgeAxioms.veracity
  | distribution : Axiom GorbowSortedKnowledgeAxioms.distribution

inductive Derives : Nat → Sentence → Type
  | axiom {σ} : Axiom σ → Derives 1 σ
  | core {σ} : GorbowPACore.Proof σ → Derives 0 σ
  | mp {N M σ τ} : Derives N (.imp σ τ) → Derives M σ → Derives (max N M) τ
  | raise {N M σ} : N ≤ M → Derives N σ → Derives M σ
  | truthNec {N σ} : Derives N σ → Derives (N+1) (truthSentence σ)
  | truthConec {N σ} : Derives N (truthSentence σ) → Derives N σ
  | knowledgeNec {N σ} : Derives N σ → Derives (N+1) (allAgentsKnow σ)
  | truthKnowledge {N σ} : Derives N (truthSentence σ) → Derives (N+1) (allAgentsKnow σ)
  | block {N σ} (used : List Sentence) :
      GorbowTheoryProof.Derivation (fun τ => Axiom τ ∨ τ ∈ used) σ →
      (∀ τ ∈ used, Derives N τ) → Derives (max 1 N) σ

def Provable (σ : Sentence) : Prop := ∃ N, Nonempty (Derives N σ)
end LogicLineages.ComputabilityKnowledge.GorbowNonreflectiveFragment
