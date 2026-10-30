module

public import LogicLineages.ComputabilityKnowledge.GorbowSortedSyntaxCode
public import LogicLineages.ComputabilityKnowledge.GorbowRevisionSemantics

@[expose] public section

/-! Fresh actual revision with sorted formula quotes. Only interpretation of
arithmetic and fixed U/u is reused; no legacy extension correspondence is
assumed. Singleton reflexive accessibility remains the explicit specialization.
Arbitrary initial predicates may contain any codes; successors contain only
sorted sentence codes. No represented Base/DCB presentation is asserted. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowSortedRevision
open GorbowSyntax GorbowSortedSyntaxCode
abbrev Ground := GorbowRevisionSemantics.Ground
abbrev Extension := GorbowRevisionSemantics.Extension
abbrev interpretation := GorbowRevisionSemantics.interpretation

def revise (g : Ground) (P : Extension) (code : Nat) : Prop :=
  ∃ σ : Sentence, formulaCode σ=code ∧ σ.realize (interpretation g P) Fin.elim0

def extensions (g : Ground) (initial : Extension) : Nat → Extension
  | 0 => initial
  | n+1 => revise g (extensions g initial n)
def stage (g : Ground) (initial : Extension) (n : Nat) : Interpretation :=
  interpretation g (extensions g initial n)

def truthSentence (σ : Sentence) : Sentence := .truth (formulaQuote 0 σ)
def allKnowledgeSentence (σ : Sentence) : Sentence := .knowledgeAll (formulaQuote 0 σ)
def knowledgeSentence (a : Nat) (σ : Sentence) : Sentence := .knowledge (Term.numeral a) (formulaQuote 0 σ)
end LogicLineages.ComputabilityKnowledge.GorbowSortedRevision
