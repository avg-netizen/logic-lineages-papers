module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.SymbolicVerifierDefinitions
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.HBAxiomTargets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.SymbolicVerifierTargets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB

/-- Exact equality to the ORIGINAL numeric checker on every original input;
the symbolic law is not inferred from this external calibration theorem. -/
def SameNumericChecker : Prop :=
  ∀ q0 : Program 5, UniversalVerifier q0 → UniversalVerifier (SymbolicVerifier.verifier q0)

/-- A genuine internal law of the explicit AST at every actual registry
occurrence, with arbitrary full-language terms and all context variables. -/
def OpenEmptyCertificate : Prop :=
  ∀ n (p : Program n) tag (q0 : Program 5),
    (nodes p)[tag]? = some ⟨5, SymbolicVerifier.verifier q0⟩ →
  ∀ ctx (index fuel context formula : Term ctx),
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (GorbowPRDefiningEquations.call tag
        (SymbolicVerifier.input index fuel context formula .zero)) .zero))

/-- ONE actual source construction retains the real CK AND real computation
producer, and derives fully symbolic empty-rejection/nonempty-input clauses
inside S. q is chosen as an explicit implementation of the SAME checker
BEFORE c/rho are constructed. No HB/internal-verifier premise occurs. -/
def SameSourceSymbolicNonempty : Prop :=
  ∃ (q0 : Program 5) (pF pR : Program 1) (c : Code)
    (tagCK : Nat) (pCK : Program 2) (tagG : Nat) (pG : Program 6),
    UniversalVerifier q0 ∧
    Actual pF pR (SymbolicVerifier.verifier q0) c ∧
    SourceBaseCompletion.SyntaxAdequate pF pR (SymbolicVerifier.verifier q0) ∧
    GorbowUniformCommonKnowledge.CodeProgram pCK ∧
    GorbowUniformCommonKnowledge.RegistryInstall pF pR (SymbolicVerifier.verifier q0) tagCK pCK ∧
    GorbowUniformCommonKnowledge.FixedPointFor pF pR (SymbolicVerifier.verifier q0) c tagCK ∧
    InstalledProducer.ProducerFor (SymbolicVerifier.verifier q0) pG ∧
    InstalledProducer.RegistryInstall pF pR (SymbolicVerifier.verifier q0) tagG pG ∧
    Nonempty (Derivation (S pF pR (SymbolicVerifier.verifier q0))
      (SymbolicVerifier.emptyClause pF)) ∧
    Nonempty (Derivation (S pF pR (SymbolicVerifier.verifier q0))
      (SymbolicVerifier.nonemptyClause pF c))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.SymbolicVerifierTargets
