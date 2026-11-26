module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderTransport.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderTransport.BundleProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
theorem unpack {n k : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (rawOld ar : Program 1) (baseX : Program 3) (tag : Nat)
 (he : (nodes p)[tag]? = some ⟨6,extra f lhs rhs t rawOld ar baseX⟩) :
 (∃ (oldTag : Nat), (nodes p)[oldTag]? = some ⟨6,CurrentNamedHeaderCertificate.extra f lhs rhs t rawOld ar baseX⟩) ∧
 (∃ (producerTag : Nat), (nodes p)[producerTag]? = some ⟨2,program⟩) := by
 have hall := ReflexivityInstalled.BundleProof.bundleInstallation
  [⟨6,CurrentNamedHeaderCertificate.extra f lhs rhs t rawOld ar baseX⟩,⟨2,program⟩] n p tag he
 exact ⟨hall _ (by simp),hall _ (by simp)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderTransport.BundleProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderTransport.BundleProof
