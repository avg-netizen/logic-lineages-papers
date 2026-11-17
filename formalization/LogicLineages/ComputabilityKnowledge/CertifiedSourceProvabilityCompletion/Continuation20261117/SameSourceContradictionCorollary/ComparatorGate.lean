module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceContradictionCorollary.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceContradictionCorollary.ComparatorGate
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB
theorem originalCorollary : Targets.Source ↔ (
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
   (GorbowUniformCommonKnowledge.closedInstance tag A falseEquality)))))) := Iff.rfl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceContradictionCorollary.ComparatorGate
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceContradictionCorollary.ComparatorGate
