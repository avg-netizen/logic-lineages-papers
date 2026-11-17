module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalHB3V2.ComparatorGate
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalHB3V2.TransportProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalHB3V2.EliminationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalHB3V2.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open SixSol20261112.Fuel NamedArithmeticGraph
open GorbowSubstitution GorbowFormulaSubstitution
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
theorem exactSource : Targets.Source := by
 intro f lhs rhs
 obtain ⟨rawOld,a,baseX,offset,pF0,pR,c,tagCK,pCK,tagG,pG,
  mtag,xtag,carrierTag,peelTag,baseTag,checkerInventoryTag,checkerTag,literalTag,publishedExtraTag,transformTag,publishedTag,
  I,N,hraw,hold,ha,hbase,hcal,hRet,hPackages,hm,h12,hcar,hpeel,hbaseProd,hInv,hCheck,hLit,hPubExtra,hTrans,hPub,
  hSyntax,hAlign,hBridge⟩ := SameSourcePublishedWitness.StatementChecks.exactSource f lhs rhs
 let t := CurrentNamedHeaderCertificate.template
 let old := CurrentQuantifierLogicalSource.selectedOld rawOld
 let pF := selected f lhs rhs rawOld a baseX pF0 pCK pG
 let q := CumulativePropositionalSource.verifier f lhs rhs old a baseX
 let root := CumulativePropositionalSource.root f lhs rhs pF pR old a baseX
 let box := InstalledProducerExtra.container pG (extra f lhs rhs rawOld a baseX pF0)
 let R := CurrentPublishedProvabilityIntroduction.RuntimeRebase.shared root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) I
 let U := S pF pR q
 have hHB : ∀ sigma : Sentence, Nonempty (Derivation U (GorbowPublishedLobReduction.hb3 pF c sigma)) := by
  intro sigma
  obtain ⟨bound,hinputs⟩ := hBridge
  let K := tags R.previous
  let innerFuel : Term 2 := .var 1
  let innerCert : Term 2 := .var 0
  let outerFuel : Term 2 := Term.numeral bound
  let raw : Term 2 := Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode (.imp (rho pF c) (prD pF c sigma))))
  let input := inputCode K R.previous.previous.current.constructorTag
   R.previous.previous.previous.previous.template.certificateTag pF0 pCK box q peelTag baseTag checkerTag pF c sigma innerFuel innerCert
  let output := CurrentPublishedProvabilityIntroduction.outputCode publishedTag pF c sigma innerFuel innerCert input
  obtain ⟨hi⟩ := hinputs sigma 2 innerFuel innerCert outerFuel
  have hguard : Derivation U (orderGuard (Term.numeral bound) outerFuel) :=
   FuelWitness.ExtractionLogicProof.orderRefl _
  have hacc : Derivation U (.imp
   (CurrentCheckerSuccessCertificate.success pF c innerFuel (LiteralCheckerSuccessBridge.value pF c sigma) innerCert)
   (accepted R.currentK.coreTag R.currentK.verifierTag (Term.numeral (Encodable.encode c)) outerFuel raw output)) :=
   .mp hi hguard
  have halign := TransportProof.liftAlignment U pF c sigma (hAlign sigma) 2
  have hcoh := CoherenceProof.calls f lhs rhs old a pF pR baseX R.currentK.verifierTag
   R.currentK.h_verifierTag (inputs (Term.numeral (Encodable.encode c)) outerFuel .zero (.add raw raw) output)
  obtain ⟨hprov⟩ := TransportProof.acceptedToProv U pF c sigma R.currentK.coreTag R.currentK.verifierTag
   outerFuel raw output halign hcoh
  exact EliminationProof.assemble U pF c sigma ⟨Hilbert.compose hprov hacc⟩
 exact ⟨rawOld,a,baseX,offset,pF0,pR,c,tagCK,pCK,tagG,pG,
  mtag,xtag,carrierTag,peelTag,baseTag,checkerInventoryTag,checkerTag,literalTag,publishedExtraTag,transformTag,publishedTag,
  I,N,hraw,hold,ha,hbase,hcal,hRet,hPackages,hm,h12,hcar,hpeel,hbaseProd,hInv,hCheck,hLit,hPubExtra,hTrans,hPub,
  hSyntax,hAlign,hBridge,hHB⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalHB3V2.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalHB3V2.Proof
