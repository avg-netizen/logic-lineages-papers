module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivityFuel.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.FuelWitness.InjectionPointwiseProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivityFuel.Proof
open GorbowSyntax GorbowTheoryProof
open TwoSol20261113.ReflexivityCertificate
/-- Compose the checked original CORE acceptance with its actual saturating
wrapper at the identical index, fuel, context, formula and certificate. -/
theorem internalSaturatedCertificate : Targets.InternalSaturatedCertificate := by
 intro k t old arithmetic x n p I vtag hv ctx values index fuel
 obtain ⟨hc⟩ := TwoSol20261113.ReflexivityCertificate.StatementChecks.exactCertificate
  k t old arithmetic x n p I ctx values index fuel
 obtain ⟨hi⟩ := SixSol20261113.FuelWitness.InjectionPointwiseProof.coreIntoVerifier
  p vtag I.qctag (TwoSol20261113.ReflexivityCertificate.checker old arithmetic x)
  hv I.hqc index fuel .zero (.add (raw I.etag values) (raw I.etag values))
  (certificate I.ctag I.qtag values)
 exact ⟨Derivation.mp hi hc⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivityFuel.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivityFuel.Proof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivityFuel.Proof.internalSaturatedCertificate
