module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule12Source.RetainedProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule12Source.PackageProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule12Source.CapabilityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule12Source.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
theorem onePublishedSource : Targets.OnePublishedSource := by
 intro f lhs rhs k t ht
 obtain ⟨old,a,baseX,offset,pF,pR,c,tagCK,pCK,tagG,pG,etag,hold,ha,hbase,hret,he⟩ :=
  RetainedProof.retainedWithBundle f lhs rhs t
 obtain ⟨mtag,btag,I,hI,hb,hm⟩ := InstallationProof.installed f lhs rhs t old a baseX pF pR etag he
 obtain ⟨xtag,hpackages⟩ := PackageProof.packages f lhs rhs old a baseX offset pF pR c tagCK pCK tagG pG mtag hret hm
 exact ⟨old,a,baseX,offset,pF,pR,c,tagCK,pCK,tagG,pG,mtag,xtag,btag,I,hI,hold,ha,hbase,hb,hm,hret,hpackages,
  CapabilityProof.compiler f lhs rhs t ht old a baseX pF pR I,
  CapabilityProof.equality f lhs rhs t old a baseX pF pR I,
  CapabilityProof.fullFormula f lhs rhs t old a baseX pF pR I,
  CapabilityProof.retention f lhs rhs t old a baseX pF pR I,
  CapabilityProof.uniform13 f lhs rhs t old a baseX pF pR I,
  CapabilityProof.uniform12 f lhs rhs t old a baseX pF pR I⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule12Source.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule12Source.Proof
