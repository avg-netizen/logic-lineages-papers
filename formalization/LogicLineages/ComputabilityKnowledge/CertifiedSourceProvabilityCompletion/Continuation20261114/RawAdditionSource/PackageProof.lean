module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionSource.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionSource.PackageProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LiteralSourceCoreMP (valid)
theorem packages (old oldA : Program 1) (baseX : Program 3) (offset : Nat)
 (pF pR : Program 1) (c : GorbowPublishedDCB.Code) (tagCK : Nat) (pCK : Program 2) (tagG : Nat) (pG : Program 6) (mtag : Nat)
 (hret : LiteralValidatedSource.Retained (logical old) (arithmetic oldA) (SaturatedAxiomLeaf.saturated baseX)
  offset pF pR c tagCK pCK tagG pG)
 (hm : (nodes (root pF pR old oldA baseX))[mtag]? = some ⟨4,LiteralRawMP.constructor⟩) :
 ∃ xtag, Packages old oldA baseX offset pF pR c mtag xtag := by
 let l := logical old
 let a := arithmetic oldA
 let x := SaturatedAxiomLeaf.saturated baseX
 have hoff : (nodes (HistoryKernel.kernel valid l a x))[offset]? = some ⟨2,HistoryAppend.append⟩ := hret.2.2.2.2.2.2.1
 obtain ⟨xtag,hax⟩ := SaturatedAxiomSource.AxiomPackageProof.axiomPackage l a baseX pF pR
 have hval := LiteralValidatedSource.ValidatorPackageProof.validatorPackage l a x offset pF pR hoff
 have hmp := LiteralSourceCoreMP.MPPackageProof.mpPackage l a x offset pF pR mtag hoff hm
 have hwit := LiteralSourceFuelWitness.Proof.witnessPackage l a x pF pR
 have hclosure := SaturatedSourceMP.ClosurePackageProof.closurePackage l a baseX offset pF pR mtag hoff hm
 have hhb2 := PublishedSourceHB2.PackageProof.hb2Package l a baseX offset pF pR c tagCK pCK tagG pG mtag hret hmp
 exact ⟨xtag,hval,hmp,hwit,hax,hclosure,hhb2⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionSource.PackageProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionSource.PackageProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionSource.PackageProof.packages
