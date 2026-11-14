module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivityInstalled.RetainedProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivityInstalled.InstallationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivityInstalled.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113
/-- Template first, then one source containing both the original retained
packages and the literal quotation/interface ASTs. All runtime values remain free. -/
theorem sameSourceCertificate : Targets.SameSourceCertificate := by
 intro k t
 obtain ⟨old,a,baseX,offset,pF,pR,c,tagCK,pCK,tagG,pG,btag,hold,hbase,hret,hbundle⟩ :=
  RetainedProof.retainedWithBundle k t
 obtain ⟨⟨mtag,hm⟩,⟨I⟩⟩ := InstallationProof.installed k t old a
  (SaturatedAxiomLeaf.saturated baseX) 4 (root pF pR old a baseX) btag hbundle
 obtain ⟨xtag,hpackages⟩ := ReflexivityPackages.StatementChecks.exactFixedWitnessIntegration
  old a baseX offset pF pR c tagCK pCK tagG pG mtag hret hm
 refine ⟨old,a,baseX,offset,pF,pR,c,tagCK,pCK,tagG,pG,mtag,xtag,I,hold,hbase,hret,hpackages,?_⟩
 intro ctx values index fuel
 have hv : (nodes (root pF pR old a baseX))[GorbowNamedInternalProvability.checkerTag pF]? =
  some ⟨5,ReflexivityFuel.checker old a (SaturatedAxiomLeaf.saturated baseX)⟩ :=
  GorbowNamedInternalProvability.Proof.exactCheckerTag 5 pF pR (verifier old a baseX)
 have hsuccess := ReflexivityFuel.StatementChecks.exactSaturatedCertificate k t old a
  (SaturatedAxiomLeaf.saturated baseX) 4 (root pF pR old a baseX) I
  (GorbowNamedInternalProvability.checkerTag pF) hv ctx values index fuel
 exact GorbowTheoryProofProof.monotonicity _ _
  (fun _ hs => List.mem_append_left _ (List.mem_append_left _ hs)) ctx _ hsuccess
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivityInstalled.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivityInstalled.Proof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivityInstalled.Proof.sameSourceCertificate
