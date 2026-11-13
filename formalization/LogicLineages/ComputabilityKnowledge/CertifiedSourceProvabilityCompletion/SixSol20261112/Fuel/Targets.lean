module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Fuel.Definitions
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.HBAxiomTargets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Fuel.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB

/-- Exact bounded-OR semantics on ALL raw numeric inputs. No Boolean premise
on opaque q0 is supplied. -/
def NativeSaturation : Prop :=
  ∀ (q0 : Program 5) index fuel context formula cert,
    (evaluate (verifier q0) (inputs index fuel context formula cert) = 1 ↔
      ∃ t, t ≤ fuel ∧ evaluate q0 (inputs index t context formula cert) = 1) ∧
    (evaluate (verifier q0) (inputs index fuel context formula cert) = 0 ∨
      evaluate (verifier q0) (inputs index fuel context formula cert) = 1)

/-- Exact original numeric checker at EACH original fuel, using only the
already paid native acceptance monotonicity and actual q0 calibration. -/
def SameNumericChecker : Prop :=
  ∀ q0 : Program 5, UniversalVerifier q0 → UniversalVerifier (verifier q0)

def OpenStep : Prop :=
  ∀ n (p : Program n) tag (q0 : Program 5), (nodes p)[tag]? = some ⟨5,verifier q0⟩ →
  ∀ ctx (index fuel context formula cert : Term ctx),
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (success tag index fuel context formula cert)
        (success tag index (.succ fuel) context formula cert)))

/-- A genuinely INTERNAL arbitrary increment, proved by actual PA induction
with every original parameter retained. No external bound/fuel schema. -/
def OpenIncrement : Prop :=
  ∀ n (p : Program n) tag (q0 : Program 5), (nodes p)[tag]? = some ⟨5,verifier q0⟩ →
  ∀ ctx (index fuel context formula cert : Term ctx),
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.all (incrementTemplate tag index fuel context formula cert)))

def OpenMonotonicity : Prop :=
  ∀ n (p : Program n) tag (q0 : Program 5), (nodes p)[tag]? = some ⟨5,verifier q0⟩ →
  ∀ ctx (index s t context formula cert : Term ctx),
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (orderGuard s t) (.imp (success tag index s context formula cert)
        (success tag index t context formula cert))))

/-- Actual source S, with the SAME original checker relation and source Pr_D
definition. The explicit verifier and real producer precede c/rho. All three
fuel laws quantify their runtime inputs INSIDE S, with no oracle premise. -/
def SameSourceFuelInvariant : Prop :=
  ∃ (q0 : Program 5) (pF pR : Program 1) (c : Code)
    (tagCK : Nat) (pCK : Program 2) (tagG : Nat) (pG : Program 6),
    UniversalVerifier q0 ∧ Actual pF pR (verifier q0) c ∧
    SourceBaseCompletion.SyntaxAdequate pF pR (verifier q0) ∧
    GorbowUniformCommonKnowledge.CodeProgram pCK ∧
    GorbowUniformCommonKnowledge.RegistryInstall pF pR (verifier q0) tagCK pCK ∧
    GorbowUniformCommonKnowledge.FixedPointFor pF pR (verifier q0) c tagCK ∧
    InstalledProducer.ProducerFor (verifier q0) pG ∧
    InstalledProducer.RegistryInstall pF pR (verifier q0) tagG pG ∧
    Nonempty (Derivation (S pF pR (verifier q0)) (stepClause pF)) ∧
    Nonempty (Derivation (S pF pR (verifier q0)) (incrementClause pF)) ∧
    Nonempty (Derivation (S pF pR (verifier q0)) (monotonicityClause pF))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.Fuel.Targets
