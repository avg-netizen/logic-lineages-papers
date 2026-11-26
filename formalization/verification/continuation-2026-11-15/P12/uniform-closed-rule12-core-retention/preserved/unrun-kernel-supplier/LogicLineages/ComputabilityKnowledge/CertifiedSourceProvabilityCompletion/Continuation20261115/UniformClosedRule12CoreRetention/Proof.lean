module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12CoreRetention.Generic.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12CoreRetention.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
/-- Specialize the fully proved arbitrary-recognizer pipeline. The old actual
leaf is the checked Rule13 extension, and the new actual AST is Rule12 with
that exact fallback. No simulation hypothesis survives. -/
theorem exactCoreRetention : Targets.InternalCoreRetention := by
 intro n p valid logical arithmetic x ot nt ptag ctag rtag dtag ho hn hp hc hr hd ctx index fuel context formula certificate
 exact Generic.Proof.internalCoreRetention UniformClosedRule12.recognizer n p valid
  (UniformClosedRule13.logicalLeaf logical) arithmetic x ot nt ptag ctag rtag dtag
  ho hn hp hc hr hd ctx index fuel context formula certificate
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12CoreRetention.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12CoreRetention.Proof
