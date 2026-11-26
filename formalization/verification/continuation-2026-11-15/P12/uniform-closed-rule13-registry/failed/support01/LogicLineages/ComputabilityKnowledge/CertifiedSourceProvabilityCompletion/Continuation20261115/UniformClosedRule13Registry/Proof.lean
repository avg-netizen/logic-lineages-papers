module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Registry.InstallationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Registry.Proof
/-- The finite installation is selected once, before all runtime inputs. -/
theorem oneRuntimePackage : Targets.OneRuntimePackage := by
 intro old arithmetic x
 obtain ⟨I⟩ := InstallationProof.finiteInstallation old arithmetic x
 refine ⟨I, ?_⟩
 intro ctx formula replacement index fuel
 exact UniformClosedRule13Certificate.StatementChecks.exactCertificate 6 (carrier old arithmetic x)
  old arithmetic x I ctx formula replacement index fuel
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Registry.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Registry.Proof
