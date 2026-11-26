module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceContradictionCorollaryV2.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceContradictionCorollaryV2.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB
/-- Printed corollary-3, retaining the same actual chosen CK and already proved
source collapse. Both instances use the SAME installed constructor tag. -/
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
   (GorbowUniformCommonKnowledge.closedInstance tag A falseEquality))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceContradictionCorollaryV2.Targets
