module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralValidatedSource.RetainedProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralValidatedSource.ValidatorPackageProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralValidatedSource.Proof
open GorbowPRProgram GorbowPRRegistry

theorem sameSourceValidatedAuxiliaries : Targets.SameSourceValidatedAuxiliaries := by
 obtain ⟨logical,arithmetic,axiomProgram,appendOffset,pF,pR,c,tagCK,pCK,tagG,pG,hret⟩ :=
  RetainedProof.constructRetained
 have hoff : (nodes (HistoryKernel.kernel valid logical arithmetic axiomProgram))[appendOffset]? =
  some ⟨2,HistoryAppend.append⟩ := hret.2.2.2.2.2.2.1
 exact ⟨logical,arithmetic,axiomProgram,appendOffset,pF,pR,c,tagCK,pCK,tagG,pG,hret,
  ValidatorPackageProof.validatorPackage logical arithmetic axiomProgram appendOffset pF pR hoff⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralValidatedSource.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralValidatedSource.Proof
