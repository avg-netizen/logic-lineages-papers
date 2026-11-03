module

public import LogicLineages.ComputabilityKnowledge.GorbowPublishedModelDefinitions
public import LogicLineages.ComputabilityKnowledge.GorbowSortedRevision

@[expose] public section
/-! Actual sorted revisions on the REAL published-D arithmetic ground.
Only persistence of the fixed D theorem-code set is intended; the revision
operator and the entire sequence of extensions are NOT assumed monotone. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowPublishedRevision
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB
open GorbowPublishedModel

def extension (pF pR : Program 1) (q : Program 5) (c : Code) (n : Nat) : Nat → Prop :=
  GorbowSortedRevision.extensions (ground pF pR q) (theoremCodes pF pR q c) n

def stage (pF pR : Program 1) (q : Program 5) (c : Code) (n : Nat) : Interpretation :=
  GorbowRevisionSemantics.interpretation (ground pF pR q) (extension pF pR q c n)

def IncludesTheorems (pF pR : Program 1) (q : Program 5) (c : Code) (P : Nat → Prop) : Prop :=
  ∀ code, theoremCodes pF pR q c code → P code

def ModusPonensClosed (P : Nat → Prop) : Prop :=
  ∀ sigma tau : Sentence,
  P (GorbowSortedSyntaxCode.formulaCode sigma) →
  P (GorbowSortedSyntaxCode.formulaCode (.imp sigma tau)) →
  P (GorbowSortedSyntaxCode.formulaCode tau)

end LogicLineages.ComputabilityKnowledge.GorbowPublishedRevision
