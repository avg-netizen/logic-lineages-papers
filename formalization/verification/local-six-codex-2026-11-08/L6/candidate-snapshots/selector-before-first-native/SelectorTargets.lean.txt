module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SelectorDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SelectorTargets
open GorbowSyntax GorbowPRProgram GorbowPublishedDCB

/-- The first conjunct of source thm:selector, independently of collapse.
This is not the whole numbered selector theorem: its chosen-CK conjunct is
deliberately absent and remains pending. -/
def FirstSelector : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ∀ A : Selector,
    Nonempty (GorbowTheoryProof.Derivation (GorbowPublishedKT.Axiom false pF pR q c)
      (GorbowBooleanTruth.biconditional (selectorTheta A) (selectedNonempty A)))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SelectorTargets
