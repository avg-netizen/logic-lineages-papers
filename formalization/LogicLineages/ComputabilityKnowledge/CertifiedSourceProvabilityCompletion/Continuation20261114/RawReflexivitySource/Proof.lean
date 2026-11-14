module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivitySource.RetainedProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivitySource.InstallationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivitySource.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113
/-- Source and every registry witness precede all runtime raw/index/fuel inputs. -/
theorem oneUniformSource : Targets.OneUniformSource := by
 obtain ⟨old,a,baseX,offset,pF,pR,c,tagCK,pCK,tagG,pG,btag,hold,hbase,hret,hbundle⟩ :=
  RetainedProof.retainedWithBundle
 have hv : (nodes (ReflexivityInstalled.root pF pR old a baseX))[GorbowNamedInternalProvability.checkerTag pF]? =
  some ⟨5,ReflexivityFuel.checker old a (SaturatedAxiomLeaf.saturated baseX)⟩ :=
  GorbowNamedInternalProvability.Proof.exactCheckerTag 5 pF pR (ReflexivityInstalled.verifier old a baseX)
 obtain ⟨⟨mtag,hm⟩,I,hI⟩ := InstallationProof.installed old a (SaturatedAxiomLeaf.saturated baseX)
  4 (ReflexivityInstalled.root pF pR old a baseX) btag (GorbowNamedInternalProvability.checkerTag pF) hbundle hv
 obtain ⟨xtag,hpackages⟩ := ReflexivityPackages.StatementChecks.exactFixedWitnessIntegration
  old a baseX offset pF pR c tagCK pCK tagG pG mtag hret hm
 refine ⟨old,a,baseX,offset,pF,pR,c,tagCK,pCK,tagG,pG,mtag,xtag,I,hI,hold,hbase,hret,hpackages,?_⟩
 intro ctx raw index fuel
 have hsuccess := RawReflexivityCertificate.StatementChecks.exactFuel
  4 (ReflexivityInstalled.root pF pR old a baseX) old a (SaturatedAxiomLeaf.saturated baseX)
  I ctx raw index fuel
 rw [hI] at hsuccess
 exact GorbowTheoryProofProof.monotonicity _ _
  (fun _ hs => List.mem_append_left _ (List.mem_append_left _ hs)) ctx _ hsuccess
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivitySource.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivitySource.Proof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivitySource.Proof.oneUniformSource
