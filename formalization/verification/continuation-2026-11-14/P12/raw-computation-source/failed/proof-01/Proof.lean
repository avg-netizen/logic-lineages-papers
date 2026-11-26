module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawComputationSource.RetainedProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawComputationSource.InstallationProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawComputationSource.PackageProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawComputationSource.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113

theorem oneUniformSource : Targets.OneUniformSource := by
 obtain ⟨old,oldA,baseX,offset,pF,pR,c,tagCK,pCK,tagG,pG,btag,hold,holdA,hbase,hret,hbundle⟩ := RetainedProof.retainedWithBundle
 have hv : (nodes (root pF pR old oldA baseX))[GorbowNamedInternalProvability.checkerTag pF]? =
  some ⟨5,RawCumulativeLogical.verifier old (arithmetic oldA) (SaturatedAxiomLeaf.saturated baseX)⟩ :=
  GorbowNamedInternalProvability.Proof.exactCheckerTag 5 pF pR (verifier old oldA baseX)
 obtain ⟨mtag,hm,I,J,K,hmp,hI,hJ,hp,hc,ha,hvtag,hK,hKp,hKc,hKa,hKv⟩ := InstallationProof.installed old oldA (SaturatedAxiomLeaf.saturated baseX)
  4 (root pF pR old oldA baseX) btag (GorbowNamedInternalProvability.checkerTag pF) hbundle hv
 have hmI : (nodes (root pF pR old oldA baseX))[I.mpTag]? = some ⟨4,LiteralRawMP.constructor⟩ := by rw [hmp]; exact hm
 obtain ⟨xtag,hpackages⟩ := PackageProof.packages old oldA baseX offset pF pR c tagCK pCK tagG pG I.mpTag hret hmI
 refine ⟨old,oldA,baseX,offset,pF,pR,c,tagCK,pCK,tagG,pG,xtag,I,J,K,
  hI,hJ,hp,hc,ha,hvtag,hK,hKp,hKc,hKa,hKv,hold,holdA,hbase,hret,hpackages,?_⟩
 intro ctx t u cert index fuel
 refine ⟨?_,?_,?_,?_,?_⟩
 · have h := RawCumulativeLogical.StatementChecks.exactFuel 4 (root pF pR old oldA baseX)
    old (arithmetic oldA) (SaturatedAxiomLeaf.saturated baseX) I.toCertificateInstallation ctx t index fuel
   exact GorbowTheoryProofProof.monotonicity _ _
    (fun _ hs => List.mem_append_left _ (List.mem_append_left _ hs)) ctx _ h
 · have h := RawCumulativeArithmetic.StatementChecks.exactFuel 4 (root pF pR old oldA baseX)
    (logical old) oldA (SaturatedAxiomLeaf.saturated baseX) J ctx t index fuel
   rw [hJ] at h
   exact GorbowTheoryProofProof.monotonicity _ _
    (fun _ hs => List.mem_append_left _ (List.mem_append_left _ hs)) ctx _ h
 · have h := RawAddSuccCertificate.StatementChecks.exactFuel 4 (root pF pR old oldA baseX)
    (logical old) (RawAddZero.arithmeticLeaf oldA) (SaturatedAxiomLeaf.saturated baseX) K ctx t u index fuel
   rw [hK] at h
   exact GorbowTheoryProofProof.monotonicity _ _
    (fun _ hs => List.mem_append_left _ (List.mem_append_left _ hs)) ctx _ h
 · have h := RawSuccReplaceCertificate.StatementChecks.exactFuel 4 (root pF pR old oldA baseX)
    (ReflexivitySource.logical old) (arithmetic oldA) (SaturatedAxiomLeaf.saturated baseX)
    (RawSuccCongruence.Proof.replacementInstallation _ _ _ _ I) ctx t u index fuel
   exact GorbowTheoryProofProof.monotonicity _ _
    (fun _ hs => List.mem_append_left _ (List.mem_append_left _ hs)) ctx _ h
 · have h := RawSuccCongruence.StatementChecks.exactCoreCongruence 4 (root pF pR old oldA baseX)
    old (arithmetic oldA) (SaturatedAxiomLeaf.saturated baseX) I ctx t u cert index fuel
   exact GorbowTheoryProofProof.monotonicity _ _
    (fun _ hs => List.mem_append_left _ (List.mem_append_left _ hs)) ctx _ h
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawComputationSource.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawComputationSource.Proof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawComputationSource.Proof.oneUniformSource
