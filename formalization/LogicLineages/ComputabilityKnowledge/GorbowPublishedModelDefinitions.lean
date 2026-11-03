module

public import LogicLineages.ComputabilityKnowledge.GorbowPublishedDCBDefinitions
public import LogicLineages.ComputabilityKnowledge.GorbowRevisionSemantics

@[expose] public section
/-! The actual published-D theorem-set interpretation, with the REAL named
overlay as its arithmetic ground. No identity with an old revision ground is
assumed. This is a consistency supplier for the concrete source presentation,
not the complete KT/FS or original-Base correspondence theorem. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowPublishedModel
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB

def namedInterpretation (pF pR : Program 1) (q : Program 5) (I : Interpretation) :
    Interpretation :=
  GorbowNamedRegistryInterpretation.interpretation (augmented pF q) pR I

def ground (pF pR : Program 1) (q : Program 5) : GorbowRevisionSemantics.Ground where
  universalRelation := fun code =>
    GorbowNamedRegistryInterpretation.relationProgram (augmented pF q) pR code = true
  universalFunction :=
    GorbowNamedRegistryInterpretation.functionProgram (augmented pF q) pR

def theoremCodes (pF pR : Program 1) (q : Program 5) (c : Code) (code : Nat) : Prop :=
  ∃ sigma : Sentence, GorbowSortedSyntaxCode.formulaCode sigma = code ∧
    Nonempty (Derivation (D pF pR q c) sigma)

/-- One agent, zero; truth and knowledge share the actual D theorem-code set.
Stage-zero compositional truth is deliberately NOT asserted. -/
def theoremModel (pF pR : Program 1) (q : Program 5) (c : Code) : Interpretation :=
  GorbowRevisionSemantics.interpretation (ground pF pR q) (theoremCodes pF pR q c)

end LogicLineages.ComputabilityKnowledge.GorbowPublishedModel
