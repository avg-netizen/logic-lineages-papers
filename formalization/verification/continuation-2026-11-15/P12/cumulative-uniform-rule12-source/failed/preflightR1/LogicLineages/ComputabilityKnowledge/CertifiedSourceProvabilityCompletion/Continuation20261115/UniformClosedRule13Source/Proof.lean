module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Source.InstallationProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Source.RetainedProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Source.PackageProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Source.Proof
/-- All witnesses come from one actual new source, selected before every runtime
input. No old source is identified with this tuple and no cross-root cast occurs. -/
theorem onePublishedSource : Targets.OnePublishedSource := by
 obtain ⟨old,a,baseX,offset,pF,pR,c,tagCK,pCK,tagG,pG,etag,hold,ha,hbase,hret,he⟩ :=
  RetainedProof.retainedWithBundle
 obtain ⟨mtag,btag,I,hI,hb,hm⟩ := InstallationProof.installed old a baseX pF pR etag he
 obtain ⟨xtag,hpackages⟩ := PackageProof.packages old a baseX offset pF pR c tagCK pCK tagG pG mtag hret hm
 exact ⟨old,a,baseX,offset,pF,pR,c,tagCK,pCK,tagG,pG,mtag,xtag,btag,I,hI,hold,ha,hbase,hb,hm,hret,hpackages,
  InstallationProof.runtime old a baseX pF pR I⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Source.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13Source.Proof
