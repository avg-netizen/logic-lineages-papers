module

public import LogicLineages.ComputabilityKnowledge.GorbowPublishedRevisionDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPublishedRevision.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB GorbowPublishedModel

/-- The two explicit extension properties must be PROVED for actual stages;
neither is a source-theory soundness or model-existence field. -/
def ExtensionModel : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ∀ P : Nat → Prop, IncludesTheorems pF pR q c P → ModusPonensClosed P →
  ∀ sigma : Sentence, D pF pR q c sigma →
    sigma.realize (GorbowRevisionSemantics.interpretation (ground pF pR q) P) Fin.elim0

/-- EVERY actual D axiom is true at EVERY actual sorted revision stage. -/
def StageAxioms : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ∀ n (sigma : Sentence), D pF pR q c sigma →
    sigma.realize (stage pF pR q c n) Fin.elim0

def StageTheorems : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ∀ n (sigma : Sentence), Nonempty (Derivation (D pF pR q c) sigma) →
    sigma.realize (stage pF pR q c n) Fin.elim0

/-- P0 is included in every Pn. No Pn⊆P(n+1) assertion is made. -/
def TheoremCodePersistence : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ∀ n, IncludesTheorems pF pR q c (extension pF pR q c n)

def Target : Prop := ExtensionModel ∧ StageAxioms ∧ StageTheorems ∧ TheoremCodePersistence

end LogicLineages.ComputabilityKnowledge.GorbowPublishedRevision.Targets
