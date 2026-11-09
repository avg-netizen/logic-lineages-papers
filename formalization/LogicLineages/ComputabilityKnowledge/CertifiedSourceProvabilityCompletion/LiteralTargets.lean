module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.LiteralDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.LiteralTargets
open GorbowSyntax GorbowPRProgram GorbowPublishedDCB

/-- A genuine ordinary bridge between different ASTs, never equality of
their numeric codes. The passed top-guarded theta implies the displayed one. -/
def DisplayedThetaBridge : Prop :=
  ∀ T : Sentence → Prop, Nonempty (GorbowTheoryProof.Derivation T
    (.imp sourceTheta literalTheta))

/-- The source's EXACT displayed truth-free counterexample is a theorem of
the original KT theory, independently of its chosen common knowledge. -/
def LiteralDirectTheta : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
    Nonempty (GorbowPublishedKT.Proof false pF pR q c literalTheta)

/-- Entire printed cor:finite at the literal displayed theta: each external
finite r has a genuine original KT tree. The E_top guards are retained in
every positive iterate, while r=0 is exactly the displayed unguarded theta. -/
def LiteralFiniteIteration : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ∀ r : Nat, Nonempty (GorbowPublishedKT.Proof false pF pR q c
    (selectedIteration topSelector r literalTheta))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.LiteralTargets
