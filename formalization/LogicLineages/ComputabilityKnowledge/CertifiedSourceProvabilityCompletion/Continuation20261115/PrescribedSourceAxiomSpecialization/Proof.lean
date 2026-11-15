module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedSourceAxiomSpecialization.RebaseProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedSourceAxiomSpecialization.SeedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedSourceAxiomSpecialization.Proof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB SixSol20261113
theorem seededSpecialization : Targets.InternalSeededSpecialization := by
 intro old arithmetic x pF pR c hA hn I mtag hm
 let J := SourceSupportProof.finiteInstallation (root pF pR old arithmetic x) old arithmetic x I
 obtain ⟨fuel,hfuel⟩ := FiniteRuleFourCertificate.StatementChecks.exactFiniteLiteralCertificate
  (UniformClosedRule13.logicalLeaf old) arithmetic x pF pR c hA hn J
 refine ⟨fuel,?_⟩
 intro n f hmem ctx G raw larger hinputs hguard
 obtain ⟨_,hc,_⟩ := hfuel (GorbowStandardInduction.universalClosure f) hmem ctx larger
 obtain ⟨hc⟩ := hc
 obtain ⟨hg⟩ := hguard
 have hseed := Hilbert.Local.mp (Hilbert.Local.base (Gamma := G) hc) hg
 obtain ⟨hprior⟩ := SeedProof.doubleCode (S pF pR (verifier old arithmetic x)) G I.coreTag
  (Term.numeral (Encodable.encode c)) larger (Term.numeral (seed f))
  (GorbowStandardInduction.universalClosure f) hseed
 exact RebaseProof.repeated old arithmetic x pF pR I mtag hm f G raw (Term.numeral (seed f))
  (Term.numeral (Encodable.encode c)) larger hinputs ⟨hprior⟩
theorem seededTrace : Targets.InternalSeededTrace := by
 intro old arithmetic x pF pR c hA I mtag hm n f sigma ctx
 have h := PrescribedRuntimeSpecialization.StatementChecks.exactPrescribedTrace
  4 (root pF pR old arithmetic x) old arithmetic (SaturatedAxiomLeaf.saturated x) I mtag hm
  n f sigma ctx (seed f)
 exact GorbowTheoryProofProof.monotonicity _ _
  (SourceSupportProof.inclusion pF pR old arithmetic x) ctx _ h
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedSourceAxiomSpecialization.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedSourceAxiomSpecialization.Proof
