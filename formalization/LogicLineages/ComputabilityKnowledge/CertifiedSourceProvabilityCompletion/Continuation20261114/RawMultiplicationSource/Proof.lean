module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationSource.RetainedProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationSource.PackageProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationSource.InstallationProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationSource.CapabilityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationSource.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113

theorem oneUniformSource : Targets.OneUniformSource := by
 obtain ⟨old,oldA,baseX,offset,pF,pR,c,tagCK,pCK,tagG,pG,btag,hold,holdA,hbase,hret,hbundle⟩ := RetainedProof.retainedWithBundle
 have hu : (nodes (root pF pR old oldA baseX))[GorbowNamedInternalProvability.checkerTag pF]? =
  some ⟨5,verifier old oldA baseX⟩ := GorbowNamedInternalProvability.Proof.exactCheckerTag 5 pF pR (verifier old oldA baseX)
 obtain ⟨I,hI⟩ := InstallationProof.installed old oldA (SaturatedAxiomLeaf.saturated baseX) 4
  (root pF pR old oldA baseX) btag (GorbowNamedInternalProvability.checkerTag pF) hbundle hu
 obtain ⟨xtag,hpackages⟩ := PackageProof.packages old oldA baseX offset pF pR c tagCK pCK tagG pG I.mpTag hret I.hmp
 have hsing := CapabilityProof.singletonCapabilities (root pF pR old oldA baseX) old oldA (SaturatedAxiomLeaf.saturated baseX) I
 have hcomp := CapabilityProof.computationCapabilities (root pF pR old oldA baseX) old oldA (SaturatedAxiomLeaf.saturated baseX) I
 have hsub : ∀ s, GorbowPRNumeralCalculation.Theory (root pF pR old oldA baseX) s →
  S pF pR (verifier old oldA baseX) s := fun _ hs => List.mem_append_left _ (List.mem_append_left _ hs)
 exact ⟨old,oldA,baseX,offset,pF,pR,c,tagCK,pCK,tagG,pG,xtag,I,hI,hold,holdA,hbase,hret,hpackages,
  CapabilityProof.liftSingleton _ _ _ _ I _ _ hsub hsing,
  CapabilityProof.liftComputation _ _ _ _ I _ _ hsub hcomp⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationSource.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationSource.Proof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationSource.Proof.oneUniformSource
