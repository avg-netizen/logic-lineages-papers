module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedAxiomSource.RetainedProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedAxiomSource.AxiomPackageProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedAxiomSource.Proof
open GorbowPRProgram GorbowPRRegistry LiteralCheckerAuxiliaries
open LiteralSourceCoreMP (valid)
/-- All four old package definitions are reconstructed at one NEW source
selection containing the saturated axiom AST. The original producer and its
actual installation stay in Retained; no earlier tuple identity is asserted. -/
theorem sameSaturatedSource : Targets.SameSaturatedSource := by
 obtain ⟨l,a,baseX,offset,pF,pR,c,tagCK,pCK,tagG,pG,mtag,hbase,hret,hm⟩ :=
  RetainedProof.constructRetained
 let x := SaturatedAxiomLeaf.saturated baseX
 have hoff : (nodes (HistoryKernel.kernel valid l a x))[offset]? =
  some ⟨2,HistoryAppend.append⟩ := hret.2.2.2.2.2.2.1
 obtain ⟨xtag,hax⟩ := AxiomPackageProof.axiomPackage l a baseX pF pR
 exact ⟨l,a,baseX,offset,pF,pR,c,tagCK,pCK,tagG,pG,mtag,xtag,hbase,hret,
  LiteralValidatedSource.ValidatorPackageProof.validatorPackage l a x offset pF pR hoff,
  LiteralSourceCoreMP.MPPackageProof.mpPackage l a x offset pF pR mtag hoff hm,
  LiteralSourceFuelWitness.Proof.witnessPackage l a x pF pR,hax⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedAxiomSource.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedAxiomSource.Proof
