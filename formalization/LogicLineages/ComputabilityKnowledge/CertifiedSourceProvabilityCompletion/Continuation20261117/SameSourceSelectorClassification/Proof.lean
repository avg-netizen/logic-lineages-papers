module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceSelectorClassification.ConsumerProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceSelectorClassification.Proof
open GorbowSyntax GorbowTheoryProof
theorem exactSource : Targets.Source := by
 obtain ⟨pF,pR,q,c,tag,p,hA,hSyntax,hCode,hInstall,hFP,hCollapse,hCorollary⟩ :=
  SameSourceContradictionCorollaryV2.StatementChecks.exactSource
 exact ⟨pF,pR,q,c,tag,p,hA,hSyntax,hCode,hInstall,hFP,hCollapse,hCorollary,
  fun A => ConsumerProof.classification pF pR q c tag hA A (hCollapse A)⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceSelectorClassification.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceSelectorClassification.Proof
