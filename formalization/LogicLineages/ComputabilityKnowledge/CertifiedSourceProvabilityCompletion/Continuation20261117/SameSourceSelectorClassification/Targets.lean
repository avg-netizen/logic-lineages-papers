module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceSelectorClassification.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceSelectorClassification.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB
/-- Both exact printed selector equivalences in ORIGINAL KT, all full-language
selectors after one chosen source. No consistency premise belongs to these
derivability claims; consistency is needed only for later nonprovability. -/
def Source : Prop :=
∃ (pF pR : Program 1) (q : Program 5) (c : Code) (tag : Nat) (p : Program 2),
 Actual pF pR q c ∧ SourceBaseCompletion.SyntaxAdequate pF pR q ∧
 GorbowUniformCommonKnowledge.CodeProgram p ∧
 GorbowUniformCommonKnowledge.RegistryInstall pF pR q tag p ∧
 GorbowUniformCommonKnowledge.FixedPointFor pF pR q c tag ∧
 (∀ A : Selector, Nonempty (Derivation (D pF pR q c)
  (GorbowBooleanTruth.biconditional (sourceC tag A)
   (everyone A (GorbowSortedSyntaxCode.formulaCode falseEquality))))) ∧
 (∀ A : Selector, Nonempty (Derivation (D pF pR q c)
  (GorbowBooleanTruth.biconditional (sourceC tag A)
   (GorbowUniformCommonKnowledge.closedInstance tag A falseEquality)))) ∧
 (∀ A : Selector,
  Nonempty (GorbowPublishedKT.Proof false pF pR q c
   (GorbowBooleanTruth.biconditional (selectorTheta A) (selectedNonempty A))) ∧
  Nonempty (GorbowPublishedKT.Proof false pF pR q c
   (GorbowBooleanTruth.biconditional (sourceC tag A) (.neg (selectedNonempty A)))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceSelectorClassification.Targets
