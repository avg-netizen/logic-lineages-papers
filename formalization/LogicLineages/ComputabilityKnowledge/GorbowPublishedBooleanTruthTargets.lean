module

public import LogicLineages.ComputabilityKnowledge.GorbowPublishedBooleanTruthDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowPublishedBooleanTruth.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB
open GorbowPublishedModel GorbowBooleanTruth GorbowSortedSyntaxCode

/-- Exact sentence-code domain on the real named ground, at arbitrary extensions. -/
def GroundGuard : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ∀ (P : Nat → Prop) n (t : Term n) env,
    (sentenceGuard t).realize (GorbowRevisionSemantics.interpretation (ground pF pR q) P) env ↔
      ∃ sigma : Sentence, formulaCode sigma =
        t.realize (GorbowRevisionSemantics.interpretation (ground pF pR q) P) env

/-- All FOUR source Boolean code constructors, with actual named-header dispatch.
Term arguments may contain arbitrary full-language universal-function calls. -/
def BooleanFunctions : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ∀ (P : Nat → Prop) n (s t : Term n) env (sigma tau : Sentence),
    s.realize (GorbowRevisionSemantics.interpretation (ground pF pR q) P) env = formulaCode sigma →
    t.realize (GorbowRevisionSemantics.interpretation (ground pF pR q) P) env = formulaCode tau →
    (negCodeTerm s).realize (GorbowRevisionSemantics.interpretation (ground pF pR q) P) env =
      formulaCode (.neg sigma) ∧
    (binaryCodeTerm 0 s t).realize (GorbowRevisionSemantics.interpretation (ground pF pR q) P) env =
      formulaCode (.imp sigma tau) ∧
    (binaryCodeTerm 1 s t).realize (GorbowRevisionSemantics.interpretation (ground pF pR q) P) env =
      formulaCode (.conj sigma tau) ∧
    (binaryCodeTerm 2 s t).realize (GorbowRevisionSemantics.interpretation (ground pF pR q) P) env =
      formulaCode (.disj sigma tau)

/-- The four literal universally CODED FS axioms at every actual positive stage.
No truth restriction is put on the encoded sentences, and stage zero is excluded. -/
def PositiveBooleanAxioms : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ∀ k : Nat,
    negAxiom.realize (GorbowPublishedRevision.stage pF pR q c (k+1)) Fin.elim0 ∧
    impAxiom.realize (GorbowPublishedRevision.stage pF pR q c (k+1)) Fin.elim0 ∧
    conjAxiom.realize (GorbowPublishedRevision.stage pF pR q c (k+1)) Fin.elim0 ∧
    disjAxiom.realize (GorbowPublishedRevision.stage pF pR q c (k+1)) Fin.elim0

def Target : Prop := GroundGuard ∧ BooleanFunctions ∧ PositiveBooleanAxioms
end LogicLineages.ComputabilityKnowledge.GorbowPublishedBooleanTruth.Targets
