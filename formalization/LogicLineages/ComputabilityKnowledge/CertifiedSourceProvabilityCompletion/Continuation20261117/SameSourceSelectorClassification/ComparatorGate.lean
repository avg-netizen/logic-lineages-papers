module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceSelectorClassification.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceSelectorClassification.ComparatorGate
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB
theorem originalSelector : Targets.Source ↔ (
∃ (pF pR : Program 1) (q : Program 5) (c : Code) (tag : Nat) (p : Program 2),
 Actual pF pR q c ∧ SourceBaseCompletion.SyntaxAdequate pF pR q ∧
 GorbowUniformCommonKnowledge.CodeProgram p ∧
 GorbowUniformCommonKnowledge.RegistryInstall pF pR q tag p ∧
 GorbowUniformCommonKnowledge.FixedPointFor pF pR q c tag ∧
 (∀ A : Selector, Nonempty (Derivation (D pF pR q c)
  (GorbowBooleanTruth.biconditional (GorbowUniformCommonKnowledge.closedInstance tag A (selectorTheta A))
   (everyone A (GorbowSortedSyntaxCode.formulaCode falseEquality))))) ∧
 (∀ A : Selector, Nonempty (Derivation (D pF pR q c)
  (GorbowBooleanTruth.biconditional (GorbowUniformCommonKnowledge.closedInstance tag A (selectorTheta A))
   (GorbowUniformCommonKnowledge.closedInstance tag A falseEquality)))) ∧
 (∀ A : Selector,
  Nonempty (GorbowPublishedKT.Proof false pF pR q c
   (GorbowBooleanTruth.biconditional (.imp (everyone A (GorbowSortedSyntaxCode.formulaCode falseEquality)) falseEquality) (selectedNonempty A))) ∧
  Nonempty (GorbowPublishedKT.Proof false pF pR q c
   (GorbowBooleanTruth.biconditional (GorbowUniformCommonKnowledge.closedInstance tag A (selectorTheta A)) (.neg (selectedNonempty A)))))) := Iff.rfl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceSelectorClassification.ComparatorGate
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceSelectorClassification.ComparatorGate
