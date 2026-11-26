module

public import LogicLineages.ComputabilityKnowledge.GorbowUniformCommonKnowledgeDefinitions
public import LogicLineages.ComputabilityKnowledge.GorbowPublishedLobReductionDefinitions
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.LiteralDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.ChosenCommonKnowledgeTransport.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB

/-- Ordinary implication transport through the SAME chosen common-knowledge
formula for arbitrary full-language sentences and selectors. The original
internal HB2/HB3 derivations remain explicit supporting hypotheses; no new
source tuple, provability predicate, or fixed-point constructor is selected. -/
def ImplicationTransport : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ∀ tag, GorbowUniformCommonKnowledge.FixedPointFor pF pR q c tag →
  (∀ sigma tau : Sentence, Nonempty (Derivation (D pF pR q c)
    (GorbowPublishedLobReduction.hb2 pF c sigma tau))) →
  (∀ sigma : Sentence, Nonempty (Derivation (D pF pR q c)
    (GorbowPublishedLobReduction.hb3 pF c sigma))) →
  ∀ (A : Selector) (sigma tau : Sentence),
    Nonempty (Derivation (D pF pR q c) (.imp sigma tau)) →
    Nonempty (Derivation (D pF pR q c)
      (.imp (GorbowUniformCommonKnowledge.closedInstance tag A sigma)
        (GorbowUniformCommonKnowledge.closedInstance tag A tau)))

/-- The missing ordinary reverse bridge between the displayed unguarded
theta and the earlier top-selector theta. Their ASTs and codes remain distinct. -/
def DisplayedThetaReverse : Prop :=
  ∀ T : Sentence → Prop,
    Nonempty (Derivation T (.imp literalTheta sourceTheta))

/-- Transport the ordinary theta equivalence through the original retained-
parameter CK formula. This conditional supporting result does not assert an
unconditional literal counterexample, select a source, or discharge internal HB. -/
def DisplayedCommonKnowledge : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ∀ tag, GorbowUniformCommonKnowledge.FixedPointFor pF pR q c tag →
  (∀ sigma tau : Sentence, Nonempty (Derivation (D pF pR q c)
    (GorbowPublishedLobReduction.hb2 pF c sigma tau))) →
  (∀ sigma : Sentence, Nonempty (Derivation (D pF pR q c)
    (GorbowPublishedLobReduction.hb3 pF c sigma))) →
  ∀ A : Selector, Nonempty (Derivation (D pF pR q c)
    (GorbowBooleanTruth.biconditional
      (GorbowUniformCommonKnowledge.closedInstance tag A literalTheta)
      (GorbowUniformCommonKnowledge.closedInstance tag A sourceTheta)))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.ChosenCommonKnowledgeTransport.Targets
