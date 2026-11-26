module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.PublishedSourceHB2.PackageProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedSourceMP.StatementChecks
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.PublishedSourceHB2.Proof
/-- Retain every existing witness/package; no source is selected or changed. -/
theorem sameSourceHB2 : Targets.SameSourceHB2 := by
 obtain ⟨l,a,baseX,offset,pF,pR,c,tagCK,pCK,tagG,pG,mtag,xtag,hbase,hret,hval,hmp,hwit,hax,hclosure⟩ :=
  SaturatedSourceMP.StatementChecks.exactSourceMP
 exact ⟨l,a,baseX,offset,pF,pR,c,tagCK,pCK,tagG,pG,mtag,xtag,hbase,hret,hval,hmp,hwit,hax,hclosure,
  PackageProof.hb2Package l a baseX offset pF pR c tagCK pCK tagG pG mtag hret hmp⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.PublishedSourceHB2.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.PublishedSourceHB2.Proof
