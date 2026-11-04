module

public import LogicLineages.ComputabilityKnowledge.GorbowPublishedAtomicTruthDefinitions
public import LogicLineages.ComputabilityKnowledge.GorbowPublishedQuantifierTruthDefinitions
public import LogicLineages.ComputabilityKnowledge.GorbowSortedKnowledgeAxioms
public import LogicLineages.ComputabilityKnowledge.GorbowSortedRevisionEventual

@[expose] public section
/-! Finite proofs in the ACTUAL published-D presentation plus the literal FS
axioms, veracity and the source's THREE theorem-only rules. Existing ordinary
Hilbert Derivation is unchanged. Optional UBF is kept a separate parameter.
The extra rules accept only closed global theorems, never open assumptions.
This is not an original-Base correspondence or internal HB assertion. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowPublishedKT
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB

inductive Axiom (withUBF : Bool) (pF pR : Program 1) (q : Program 5) (c : Code) :
    Sentence → Prop where
  | d (sigma : Sentence) : D pF pR q c sigma → Axiom withUBF pF pR q c sigma
  | negation : Axiom withUBF pF pR q c GorbowBooleanTruth.negAxiom
  | implication : Axiom withUBF pF pR q c GorbowBooleanTruth.impAxiom
  | conjunction : Axiom withUBF pF pR q c GorbowBooleanTruth.conjAxiom
  | disjunction : Axiom withUBF pF pR q c GorbowBooleanTruth.disjAxiom
  | universal : Axiom withUBF pF pR q c GorbowSortedQuantifierTruth.forallAxiom
  | existential : Axiom withUBF pF pR q c GorbowSortedQuantifierTruth.existsAxiom
  | atomic {n m : Nat} (R : Formula m) (names : Fin n → Fin m) :
      GorbowRevisionComposition.AtomicMinus R → Function.Injective names →
      GorbowNameDictionary.Covers R names →
      Axiom withUBF pF pR q c (GorbowAtomicTruth.atomicAxiom R names)
  | veracity : Axiom withUBF pF pR q c GorbowSortedKnowledgeAxioms.veracity
  | barcan : withUBF = true →
      Axiom withUBF pF pR q c GorbowSortedQuantifierTruth.barcanAxiom

/-- Ordinary blocks are REAL existing Hilbert derivations from the explicit
axioms, and all intervening ordinary MP/generalization steps are available.
Only the three literal source theorem rules extend that ordinary calculus. -/
inductive Proof (withUBF : Bool) (pF pR : Program 1) (q : Program 5) (c : Code) :
    {n : Nat} → Formula n → Type where
  | ordinary {n} {phi : Formula n} :
      Derivation (Axiom withUBF pF pR q c) phi → Proof withUBF pF pR q c phi
  | mp {n} {a b : Formula n} :
      Proof withUBF pF pR q c (.imp a b) → Proof withUBF pF pR q c a →
      Proof withUBF pF pR q c b
  | generalize {n} {a : Formula (n+1)} :
      Proof withUBF pF pR q c a → Proof withUBF pF pR q c (.all a)
  | truthIntroduction {sigma : Sentence} : Proof withUBF pF pR q c sigma →
      Proof withUBF pF pR q c (GorbowSortedRevision.truthSentence sigma)
  | truthElimination {sigma : Sentence} :
      Proof withUBF pF pR q c (GorbowSortedRevision.truthSentence sigma) →
      Proof withUBF pF pR q c sigma
  | knowledgeNecessitation {sigma : Sentence} : Proof withUBF pF pR q c sigma →
      Proof withUBF pF pR q c (GorbowSortedRevisionEventual.allAgentsKnow sigma)

/-- An explicit finite proof bound; no minimality assertion is intended. -/
def threshold {withUBF pF pR q c} :
    {n : Nat} → {phi : Formula n} → Proof withUBF pF pR q c phi → Nat
  | _,_,.ordinary _ => 1
  | _,_,.mp p r => max (threshold p) (threshold r)
  | _,_,.generalize p => threshold p
  | _,_,.truthIntroduction p => threshold p + 1
  | _,_,.truthElimination p => threshold p
  | _,_,.knowledgeNecessitation p => threshold p + 1

def UniformThreshold (pF pR : Program 1) (q : Program 5) (c : Code)
    {n : Nat} (phi : Formula n) (N : Nat) : Prop :=
  ∀ k, N ≤ k → ∀ env : Fin n → Nat,
    phi.realize (GorbowPublishedRevision.stage pF pR q c k) env

end LogicLineages.ComputabilityKnowledge.GorbowPublishedKT
