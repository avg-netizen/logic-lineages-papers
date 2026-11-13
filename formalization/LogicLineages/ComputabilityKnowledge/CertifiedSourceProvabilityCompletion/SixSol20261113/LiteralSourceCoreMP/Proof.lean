module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSourceCoreMP.RetainedExtraProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSourceCoreMP.MPPackageProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralValidatedSource.ValidatorPackageProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSourceCoreMP.Proof
open GorbowPRProgram GorbowPRRegistry

theorem sameSourceCoreMP : Targets.SameSourceCoreMP := by
 obtain ⟨l,a,x,offset,pF,pR,c,tagCK,pCK,tagG,pG,mtag,hret,hm⟩ :=
  RetainedExtraProof.constructRetainedExtra
 have hoff : (nodes (HistoryKernel.kernel valid l a x))[offset]? =
  some ⟨2,HistoryAppend.append⟩ := hret.2.2.2.2.2.2.1
 exact ⟨l,a,x,offset,pF,pR,c,tagCK,pCK,tagG,pG,mtag,hret,
  LiteralValidatedSource.ValidatorPackageProof.validatorPackage l a x offset pF pR hoff,
  MPPackageProof.mpPackage l a x offset pF pR mtag hoff hm⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSourceCoreMP.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSourceCoreMP.Proof
