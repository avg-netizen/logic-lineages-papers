module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalAdoption.ComparatorGate
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalAdoption.Proof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
/-- One invocation supplies BOTH existential endpoints. Their exact common
witness tuple is visible below; no conjunction-to-common-witness inference. -/
theorem together : Targets.Together := by
 obtain ⟨rawOld,a,baseX,offset,pF0,pR,c,tagCK,pCK,tagG,pG,
  mtag,xtag,carrierTag,peelTag,baseTag,checkerInventoryTag,checkerTag,literalTag,publishedExtraTag,transformTag,publishedTag,
  I,N,hraw,hold,ha,hbase,hcal,hRet,hPackages,hm,h12,hcar,hpeel,hbaseProd,hInv,hCheck,hLit,hPubExtra,hTrans,hPub,
  hSyntax,hAlign,hBridge,hHB3S,hA,hAdequate,hCode,hInstall,hFP,hHB2S,hHB2D,hHB3D,hLob,hCollapse⟩ :=
  SameSourceLobCollapse.StatementChecks.exactSource (Formula.equal (Term.zero : Term 1) .zero) .zero .zero
 let pF := SameSourceLobCollapse.selected (Formula.equal (Term.zero : Term 1) .zero) .zero .zero rawOld a baseX pF0 pCK pG
 let q := CumulativePropositionalSource.verifier (Formula.equal (Term.zero : Term 1) .zero) .zero .zero
  (CurrentQuantifierLogicalSource.selectedOld rawOld) a baseX
 exact ⟨⟨pF,pR,q,c,tagCK,pCK,hA,hAdequate,hCode,hInstall,hFP,hHB2D,hHB3D⟩,
  ⟨pF,pR,q,c,tagCK,pCK,hA,hAdequate,hCode,hInstall,hFP,hCollapse⟩⟩

/-- Exactly the unchanged original selected certified-presentation target. -/
theorem originalSelected : SourceBaseCompletion.SelectedVerifierTargets.SelectedCertifiedPresentation := together.1
/-- Exactly the unchanged original selector-uniform source collapse target. -/
theorem originalCollapse : CollapseTargets.SourceCollapse := together.2
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalAdoption.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalAdoption.Proof
