module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.InternalFiniteSourceDefinitions
public import LogicLineages.ComputabilityKnowledge.SourceBaseCompletion.SelectedVerifierTargets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.HBAxiomTargets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB

/-- The unchanged full internal-HB supplier, kept apart from the finite axiom
case. Its HB2/HB3 clauses are not paid by the declarations below. -/
def OriginalSelectedCertifiedPresentation : Prop :=
  SourceBaseCompletion.SelectedVerifierTargets.SelectedCertifiedPresentation

/-- The exact finite ADDITIONAL axiom list of D=S+rho. Logical/PA schemata
are intrinsic constructors of Derivation, not entries in this finite list. -/
def additionalDAxioms (pF pR : Program 1) (q : Program 5) (c : Code) : List Sentence :=
  axiomsS pF pR q ++ [rho pF c]

/-- Strengthened external HB1: D proofs are certified in S itself, for the
literal Pr_D=Pr_S(rho -> sigma), before any embedding into D. -/
def CertificationInS : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ∀ sigma : Sentence, Nonempty (Derivation (D pF pR q c) sigma) →
    Nonempty (Derivation (S pF pR q) (prD pF c sigma))

/-- A symbolic formula-code input, genuinely universally bound INSIDE S,
with the actual chosen Pr_D template. No standard-model completeness or
symbolic verifier-preservation assumption appears here. -/
def InternalAdditionalDAxioms : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
    (∀ sigma : Sentence, D pF pR q c sigma ↔ sigma ∈ additionalDAxioms pF pR q c) ∧
    Nonempty (Derivation (S pF pR q) (.all
      (.imp (InternalFiniteSource.codeList (additionalDAxioms pF pR q c))
        (GorbowPublishedLobReduction.provabilityTemplate pF c))))

/-- The internal source-axiom rule coexists with the same installed CK and
source Base contract. All construction witnesses precede all object inputs. -/
def SameSourceAdditionalDAxioms : Prop :=
  ∃ (pF pR : Program 1) (q : Program 5) (c : Code) (tag : Nat) (p : Program 2),
    Actual pF pR q c ∧ SourceBaseCompletion.SyntaxAdequate pF pR q ∧
    GorbowUniformCommonKnowledge.CodeProgram p ∧
    GorbowUniformCommonKnowledge.RegistryInstall pF pR q tag p ∧
    GorbowUniformCommonKnowledge.FixedPointFor pF pR q c tag ∧
    Nonempty (Derivation (S pF pR q) (.all
      (.imp (InternalFiniteSource.codeList (additionalDAxioms pF pR q c))
        (GorbowPublishedLobReduction.provabilityTemplate pF c))))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.HBAxiomTargets
