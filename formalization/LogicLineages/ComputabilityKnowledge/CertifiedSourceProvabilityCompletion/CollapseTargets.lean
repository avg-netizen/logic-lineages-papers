module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.CollapseDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.CollapseTargets
open GorbowSyntax GorbowPRProgram GorbowPublishedDCB GorbowTheoryProof

/-- Conditional source-shaped consumer, keeping the exact THREE required
internal derivations explicit. This does not pay their arithmetic supplier. -/
def LocalCollapseReduction : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ∀ tag, GorbowUniformCommonKnowledge.FixedPointFor pF pR q c tag →
  ∀ A : Selector,
    Nonempty (Derivation (D pF pR q c) (localHB1 pF c tag A)) →
    Nonempty (Derivation (D pF pR q c) (localHB2 pF c tag A)) →
    Nonempty (Derivation (D pF pR q c) (localHB3 pF c tag A)) →
    Nonempty (Derivation (D pF pR q c) (GorbowBooleanTruth.biconditional
      (sourceC tag A) (everyone A (GorbowSortedSyntaxCode.formulaCode falseEquality))))

/-- The smaller ACTUAL certified-presentation task. All witnesses precede
every selector. Standard calibration is not substituted for internal HB. -/
def SelectedLocalHB : Prop :=
  ∃ (pF pR : Program 1) (q : Program 5) (c : Code) (tag : Nat) (p : Program 2),
    Actual pF pR q c ∧ SourceBaseCompletion.SyntaxAdequate pF pR q ∧
    GorbowUniformCommonKnowledge.CodeProgram p ∧
    GorbowUniformCommonKnowledge.RegistryInstall pF pR q tag p ∧
    GorbowUniformCommonKnowledge.FixedPointFor pF pR q c tag ∧
    ∀ A : Selector,
      Nonempty (Derivation (D pF pR q c) (localHB1 pF c tag A)) ∧
      Nonempty (Derivation (D pF pR q c) (localHB2 pF c tag A)) ∧
      Nonempty (Derivation (D pF pR q c) (localHB3 pF c tag A))

/-- The entire literal source collapse at one actual source tuple and its
same installed chosen CK formula, with no HB or provability oracle premise. -/
def SourceCollapse : Prop :=
  ∃ (pF pR : Program 1) (q : Program 5) (c : Code) (tag : Nat) (p : Program 2),
    Actual pF pR q c ∧ SourceBaseCompletion.SyntaxAdequate pF pR q ∧
    GorbowUniformCommonKnowledge.CodeProgram p ∧
    GorbowUniformCommonKnowledge.RegistryInstall pF pR q tag p ∧
    GorbowUniformCommonKnowledge.FixedPointFor pF pR q c tag ∧
    ∀ A : Selector, Nonempty (Derivation (D pF pR q c)
      (GorbowBooleanTruth.biconditional (sourceC tag A)
        (everyone A (GorbowSortedSyntaxCode.formulaCode falseEquality))))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.CollapseTargets
