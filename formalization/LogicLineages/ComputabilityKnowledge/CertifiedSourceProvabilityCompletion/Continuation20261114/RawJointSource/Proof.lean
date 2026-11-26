module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawJointSource.RetainedProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawJointSource.InstallationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawJointSource.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113
/-- Rebuild once with both calibrated leaves, then retain both certificate
families at the same source, never replacing a previously selected leaf. -/
theorem oneUniformSource : Targets.OneUniformSource := by
 obtain ⟨old,oldA,baseX,offset,pF,pR,c,tagCK,pCK,tagG,pG,btag,hold,holdA,hbase,hret,hbundle⟩ :=
  RetainedProof.retainedWithBundle
 have hv : (nodes (root pF pR old oldA baseX))[GorbowNamedInternalProvability.checkerTag pF]? =
  some ⟨5,ReflexivityFuel.checker old (RawAddZero.arithmeticLeaf oldA) (SaturatedAxiomLeaf.saturated baseX)⟩ :=
  GorbowNamedInternalProvability.Proof.exactCheckerTag 5 pF pR (verifier old oldA baseX)
 obtain ⟨⟨mtag,hm⟩,I,J,hI,hJ,hp,hc,ha,hvtag⟩ := InstallationProof.installed old oldA (SaturatedAxiomLeaf.saturated baseX)
  4 (root pF pR old oldA baseX) btag (GorbowNamedInternalProvability.checkerTag pF) hbundle hv
 obtain ⟨xtag,hpackages⟩ := ReflexivityPackages.StatementChecks.exactFixedWitnessIntegration
  old (RawAddZero.arithmeticLeaf oldA) baseX offset pF pR c tagCK pCK tagG pG mtag hret hm
 refine ⟨old,oldA,baseX,offset,pF,pR,c,tagCK,pCK,tagG,pG,mtag,xtag,I,J,
  hI,hJ,hp,hc,ha,hvtag,hold,holdA,hbase,hret,hpackages,?_⟩
 intro ctx raw index fuel
 constructor
 · have hsuccess := RawReflexivityCertificate.StatementChecks.exactFuel
    4 (root pF pR old oldA baseX) old (RawAddZero.arithmeticLeaf oldA) (SaturatedAxiomLeaf.saturated baseX)
    I ctx raw index fuel
   rw [hI] at hsuccess
   exact GorbowTheoryProofProof.monotonicity _ _
    (fun _ hs => List.mem_append_left _ (List.mem_append_left _ hs)) ctx _ hsuccess
 · have hsuccess := RawAddZeroCertificate.StatementChecks.exactFuel
    4 (root pF pR old oldA baseX) (ReflexivitySource.logical old) oldA (SaturatedAxiomLeaf.saturated baseX)
    J ctx raw index fuel
   rw [hJ,hI] at hsuccess
   exact GorbowTheoryProofProof.monotonicity _ _
    (fun _ hs => List.mem_append_left _ (List.mem_append_left _ hs)) ctx _ hsuccess
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawJointSource.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawJointSource.Proof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawJointSource.Proof.oneUniformSource
