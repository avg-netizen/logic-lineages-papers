module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentCertificate.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentCertificate.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113
/-- One preselected uniform installation before f and runtime environment.
Original formulaValidator1(A) and actual compiled conclusion identification
are proof duties, not hypotheses. The sole local guards are closed old raw
coordinates and the closed replacement required by the original recognizer.
Actual certificate NUMBER is the run bound; arbitrary index/fuel include zero. -/
def InternalRuntimeCertificate : Prop :=
 ∀ arity (p : Program arity) (old arithmetic : Program 1) (x : Program 3)
 (I : UniformClosedRule13Certificate.Installation p old arithmetic x),
 ∀ n inputs (e : FixedFormulaSubstitution.Environment n 1 inputs) (f : Formula n)
 ctx (G : List (Formula ctx)) (raw : List.Vector (Term ctx) inputs) (replacement index fuel : Term ctx),
 (∀ i : Fin inputs, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (Continuation20261114.RawReflexivityDispatcher.valid I.vtag (raw.get i)))) →
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (Continuation20261114.RawReflexivityDispatcher.valid I.vtag replacement)) →
 let A := FixedFormulaSubstitution.formulaValue I.ctag I.atag raw f e
 let F := conclusion I.ctag I.atag e f raw replacement
 let code := UniformClosedRule13Certificate.certificate I.ctag I.constructorTag A replacement
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.conj
   (.equal (LiteralCheckerAcceptance.runCall I.iteratorTag I.ptag index fuel code) (output I.ptag I.ctag F))
   (.conj
    (.equal (LiteralCheckerAcceptance.coreCall I.coreTag index fuel .zero (.add F F) code) (.succ .zero))
    (SixSol20261112.Fuel.success I.verifierTag index fuel .zero (.add F F) code))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeEnvironmentCertificate.Targets
