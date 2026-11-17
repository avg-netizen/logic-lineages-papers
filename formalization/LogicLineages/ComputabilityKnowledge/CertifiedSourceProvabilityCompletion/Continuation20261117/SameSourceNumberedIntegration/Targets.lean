module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceNumberedIntegration.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceNumberedIntegration.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB
/-- Reconciliation of all six NUMBERED source scopes at one actual tuple.
The displayed literalTheta finite iterations are not identified with
selectorTheta(top) or its different chosen-CK code. Unnumbered CK transport
and nonprovability narrative are deliberately outside this contract. -/
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
   (GorbowBooleanTruth.biconditional (sourceC tag A) (.neg (selectedNonempty A))))) ∧
 (∀ (A : Selector) (sigma tau : Sentence),
  (Nonempty (Derivation (D pF pR q c) sigma) →
   Nonempty (Derivation (D pF pR q c) (everyone A (GorbowSortedSyntaxCode.formulaCode sigma)))) ∧
  Nonempty (Derivation (D pF pR q c) (GorbowSelectedDistribution.selectedDistribution A sigma tau)) ∧
  Nonempty (Derivation (D pF pR q c)
   (.imp (prD pF c sigma) (everyone A (GorbowSortedSyntaxCode.formulaCode sigma))))) ∧
 (∀ r : Nat, Nonempty (GorbowPublishedKT.Proof false pF pR q c
  (selectedIteration topSelector r literalTheta))) ∧
 (∀ withUBF : Bool, ¬ Nonempty (GorbowPublishedKT.Proof withUBF pF pR q c falseEquality))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceNumberedIntegration.Targets
