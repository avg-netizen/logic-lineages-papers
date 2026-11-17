module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalAdoption.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalAdoption.ComparatorGate
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB
theorem originalSelected : Targets.OriginalSelected ↔ (
∃ (pF pR : Program 1) (q : Program 5) (c : Code) (tag : Nat) (p : Program 2),
    Actual pF pR q c ∧ SourceBaseCompletion.SyntaxAdequate pF pR q ∧
    GorbowUniformCommonKnowledge.CodeProgram p ∧
    GorbowUniformCommonKnowledge.RegistryInstall pF pR q tag p ∧
    GorbowUniformCommonKnowledge.FixedPointFor pF pR q c tag ∧
    (∀ sigma tau : Sentence, Nonempty (Derivation (D pF pR q c)
      (GorbowPublishedLobReduction.hb2 pF c sigma tau))) ∧
    (∀ sigma : Sentence, Nonempty (Derivation (D pF pR q c)
      (GorbowPublishedLobReduction.hb3 pF c sigma)))) := Iff.rfl
theorem originalCollapse : Targets.OriginalCollapse ↔ (
∃ (pF pR : Program 1) (q : Program 5) (c : Code) (tag : Nat) (p : Program 2),
    Actual pF pR q c ∧ SourceBaseCompletion.SyntaxAdequate pF pR q ∧
    GorbowUniformCommonKnowledge.CodeProgram p ∧
    GorbowUniformCommonKnowledge.RegistryInstall pF pR q tag p ∧
    GorbowUniformCommonKnowledge.FixedPointFor pF pR q c tag ∧
    ∀ A : Selector, Nonempty (Derivation (D pF pR q c)
      (GorbowBooleanTruth.biconditional (sourceC tag A)
        (everyone A (GorbowSortedSyntaxCode.formulaCode falseEquality))))) := Iff.rfl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalAdoption.ComparatorGate
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalAdoption.ComparatorGate
