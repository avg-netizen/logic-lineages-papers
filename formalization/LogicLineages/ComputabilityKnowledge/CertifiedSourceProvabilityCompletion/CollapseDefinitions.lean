module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SelectorDefinitions
public import LogicLineages.ComputabilityKnowledge.GorbowUniformCommonKnowledgeDefinitions
public import LogicLineages.ComputabilityKnowledge.GorbowPublishedLobReductionDefinitions
public import LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.BaseDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion
open GorbowSyntax GorbowPRProgram GorbowPublishedDCB

/-- One instance of the same installed retained-parameter source CK formula. -/
def sourceC (tag : Nat) (A : Selector) : Sentence :=
  GorbowUniformCommonKnowledge.closedInstance tag A (selectorTheta A)

def collapseDelta (tag : Nat) (A : Selector) : Sentence :=
  .imp (sourceC tag A) (everyone A (GorbowSortedSyntaxCode.formulaCode falseEquality))

def localHB1 (pF : Program 1) (c : Code) (tag : Nat) (A : Selector) : Sentence :=
  let d := GorbowPublishedLobReduction.delta pF c (collapseDelta tag A)
  GorbowPublishedLobReduction.hb2 pF c d (.imp (prD pF c d) (collapseDelta tag A))

def localHB2 (pF : Program 1) (c : Code) (tag : Nat) (A : Selector) : Sentence :=
  let d := GorbowPublishedLobReduction.delta pF c (collapseDelta tag A)
  GorbowPublishedLobReduction.hb2 pF c (prD pF c d) (collapseDelta tag A)

def localHB3 (pF : Program 1) (c : Code) (tag : Nat) (A : Selector) : Sentence :=
  GorbowPublishedLobReduction.hb3 pF c
    (GorbowPublishedLobReduction.delta pF c (collapseDelta tag A))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion
