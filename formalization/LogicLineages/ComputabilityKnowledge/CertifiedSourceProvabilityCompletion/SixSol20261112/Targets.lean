module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.CollapseTargets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB

/-- Original paper12 thm:collapse, unchanged and still unpaid by the component
below. The same installed retained-parameter formula supplies c_A. -/
def OriginalSourceCollapse : Prop := CollapseTargets.SourceCollapse

/-- The complete source corollary at paper12 lines 211--213, retaining ONE
actual syntax-adequate tuple and ONE installed CK formula before every A.
This original target is separate from the contradiction component below. -/
def OriginalCommonBeliefCorollary : Prop :=
  ∃ (pF pR : Program 1) (q : Program 5) (c : Code) (tag : Nat) (p : Program 2),
    Actual pF pR q c ∧ SourceBaseCompletion.SyntaxAdequate pF pR q ∧
    GorbowUniformCommonKnowledge.CodeProgram p ∧
    GorbowUniformCommonKnowledge.RegistryInstall pF pR q tag p ∧
    GorbowUniformCommonKnowledge.FixedPointFor pF pR q c tag ∧
    ∀ A : Selector, Nonempty (Derivation (D pF pR q c)
      (GorbowBooleanTruth.biconditional (sourceC tag A)
        (GorbowUniformCommonKnowledge.closedInstance tag A falseEquality)))

/-- A genuine ordinary internal derivation at every ACTUAL installed tuple.
The fixed-point equivalence is derived from its concrete installed program,
not supplied as an extra CK/HB oracle premise. -/
def InstalledContradictionReduction : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code) (tag : Nat) (p : Program 2),
    Actual pF pR q c → GorbowUniformCommonKnowledge.CodeProgram p →
    GorbowUniformCommonKnowledge.RegistryInstall pF pR q tag p →
    ∀ A : Selector, Nonempty (Derivation (D pF pR q c)
      (GorbowBooleanTruth.biconditional
        (GorbowUniformCommonKnowledge.closedInstance tag A falseEquality)
        (everyone A (GorbowSortedSyntaxCode.formulaCode falseEquality))))

/-- Existence discharges all installation/calibration premises and retains
the complete chosen CK contract in the SAME source-Base construction. -/
def SameSourceContradictionReduction : Prop :=
  ∃ (pF pR : Program 1) (q : Program 5) (c : Code) (tag : Nat) (p : Program 2),
    Actual pF pR q c ∧ SourceBaseCompletion.SyntaxAdequate pF pR q ∧
    GorbowUniformCommonKnowledge.CodeProgram p ∧
    GorbowUniformCommonKnowledge.RegistryInstall pF pR q tag p ∧
    GorbowUniformCommonKnowledge.FixedPointFor pF pR q c tag ∧
    ∀ A : Selector, Nonempty (Derivation (D pF pR q c)
      (GorbowBooleanTruth.biconditional
        (GorbowUniformCommonKnowledge.closedInstance tag A falseEquality)
        (everyone A (GorbowSortedSyntaxCode.formulaCode falseEquality))))

/-- Only a downstream consumer: the complete original collapse still has to
be paid independently before this implication closes the original corollary. -/
def CommonBeliefFromCollapse : Prop :=
  OriginalSourceCollapse → OriginalCommonBeliefCorollary

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Targets
