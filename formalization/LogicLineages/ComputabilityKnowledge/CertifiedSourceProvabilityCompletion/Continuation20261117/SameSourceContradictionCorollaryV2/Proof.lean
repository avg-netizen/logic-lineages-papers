module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceContradictionCorollaryV2.ComparatorGate
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceContradictionCorollaryV2.ConsumerProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceContradictionCorollaryV2.Proof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB
open GorbowSortedSyntaxCode
theorem exactSource : Targets.Source := by
 obtain ⟨pF,pR,q,c,tag,p,hA,hSyntax,hCode,hInstall,hFP,hCollapse⟩ :=
  SameSourceOriginalAdoption.StatementChecks.exactOriginalCollapse
 exact ⟨pF,pR,q,c,tag,p,hA,hSyntax,hCode,hInstall,hFP,hCollapse,
  fun A => ConsumerProof.corollary pF pR q c tag hA hFP A (hCollapse A)⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceContradictionCorollaryV2.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceContradictionCorollaryV2.Proof
