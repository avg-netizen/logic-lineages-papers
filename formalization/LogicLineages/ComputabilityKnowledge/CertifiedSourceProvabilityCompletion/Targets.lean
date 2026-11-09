module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Definitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Targets
open GorbowSyntax GorbowPRProgram GorbowPublishedDCB

/-- The literal closed contradiction's atomic truth clause, inside the
original KT ordinary Hilbert blocks, for every actual source presentation. -/
def AtomicContradictionTruth : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
    Nonempty (GorbowTheoryProof.Derivation (GorbowPublishedKT.Axiom false pF pR q c)
      (.imp (GorbowSortedRevision.truthSentence falseEquality) falseEquality))

/-- The truth-free counterexample sentence is itself a theorem of original
KT, independently of its chosen common-knowledge sentence. -/
def DirectTheta : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
    Nonempty (GorbowPublishedKT.Proof false pF pR q c sourceTheta)

/-- The entire printed cor:finite: separate actual KT derivations for every
external finite r. The source E_top is retained at every iteration. -/
def FiniteIteration : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ∀ r : Nat, Nonempty (GorbowPublishedKT.Proof false pF pR q c
    (selectedIteration topSelector r sourceTheta))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Targets
