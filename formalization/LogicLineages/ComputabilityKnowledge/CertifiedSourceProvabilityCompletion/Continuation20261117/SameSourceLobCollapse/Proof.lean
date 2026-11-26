module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceLobCollapse.ComparatorGate
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceLobCollapse.ConsumerProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceLobCollapse.Proof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
attribute [local irreducible] GorbowPublishedDCB.rho GorbowPublishedDCB.prD
theorem exactSource : Targets.Source := by
 intro f lhs rhs
 obtain ⟨rawOld,a,baseX,offset,pF0,pR,c,tagCK,pCK,tagG,pG,
  mtag,xtag,carrierTag,peelTag,baseTag,checkerInventoryTag,checkerTag,literalTag,publishedExtraTag,transformTag,publishedTag,
  I,N,hraw,hold,ha,hbase,hcal,hRet,hPackages,hm,h12,hcar,hpeel,hbaseProd,hInv,hCheck,hLit,hPubExtra,hTrans,hPub,
  hSyntax,hAlign,hBridge,hHB3⟩ := SameSourceOriginalHB3V2.StatementChecks.exactSource f lhs rhs
 let old := CurrentQuantifierLogicalSource.selectedOld rawOld
 let pF := selected f lhs rhs rawOld a baseX pF0 pCK pG
 let q := CumulativePropositionalSource.verifier f lhs rhs old a baseX
 have hretain := hRet
 rcases hretain with ⟨_,_,_,_,_,_,_,_,hA,hAdequate,hCode,hInstall,hFP,_⟩
 have hpackages := hPackages
 rcases hpackages with ⟨_,_,_,_,_,hHB2⟩
 have h2 : ∀ sigma tau : Sentence, Nonempty (Derivation (S pF pR q)
  (GorbowPublishedLobReduction.hb2 pF c sigma tau)) := hHB2
 obtain ⟨h2D,h3D,hLob,hCollapse⟩ := ConsumerProof.consumers pF pR q c tagCK hA hFP h2 hHB3
 exact ⟨rawOld,a,baseX,offset,pF0,pR,c,tagCK,pCK,tagG,pG,
  mtag,xtag,carrierTag,peelTag,baseTag,checkerInventoryTag,checkerTag,literalTag,publishedExtraTag,transformTag,publishedTag,
  I,N,hraw,hold,ha,hbase,hcal,hRet,hPackages,hm,h12,hcar,hpeel,hbaseProd,hInv,hCheck,hLit,hPubExtra,hTrans,hPub,
  hSyntax,hAlign,hBridge,hHB3,hA,hAdequate,hCode,hInstall,hFP,h2,h2D,h3D,hLob,hCollapse⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceLobCollapse.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceLobCollapse.Proof
