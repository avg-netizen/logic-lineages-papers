module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourcePublishedWitness.ComparatorGate
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourcePublishedWitness.SourceBridge
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph
/-- The input bridge and original published introduction share literally one
source/index/installation and the actual new box offsets. -/
theorem bridge (f : Formula 1) (lhs rhs : Term 1) (rawOld a : Program 1) (baseX : Program 3)
 (pF0 pR : Program 1) (pCK : Program 2) (box : Program 6) (c : Code)
 (hA : Actual (GorbowNamedInternalProvability.augment (GorbowNamedInternalProvability.augment pF0 pCK) box) pR
  (CumulativePropositionalSource.verifier f lhs rhs (CurrentQuantifierLogicalSource.selectedOld rawOld) a baseX) c)
 (hbase : ∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v)
 (I : CumulativePropositionalSource.JointInstallation
  (CumulativePropositionalSource.root f lhs rhs
   (GorbowNamedInternalProvability.augment (GorbowNamedInternalProvability.augment pF0 pCK) box) pR
   (CurrentQuantifierLogicalSource.selectedOld rawOld) a baseX)
  f lhs rhs CurrentNamedHeaderCertificate.template (CurrentQuantifierLogicalSource.selectedOld rawOld) a (SaturatedAxiomLeaf.saturated baseX))
 (N : CurrentExistentialIntroductionProgram.LogicalInterface.Nodes
  (CumulativePropositionalSource.root f lhs rhs
   (GorbowNamedInternalProvability.augment (GorbowNamedInternalProvability.augment pF0 pCK) box) pR
   (CurrentQuantifierLogicalSource.selectedOld rawOld) a baseX))
 (carrierTag peelTag baseTag checkerInventoryTag checkerTag transformTag publishedTag : Nat)
 (hcarrier : (nodes (CumulativePropositionalSource.root f lhs rhs
   (GorbowNamedInternalProvability.augment (GorbowNamedInternalProvability.augment pF0 pCK) box) pR
   (CurrentQuantifierLogicalSource.selectedOld rawOld) a baseX))[carrierTag]? =
  some ⟨6,CurrentStructuralProducerInventory.carrier f lhs rhs CurrentNamedHeaderCertificate.template (CurrentQuantifierLogicalSource.selectedOld rawOld) a baseX pF0⟩)
 (hpeel : (nodes (CumulativePropositionalSource.root f lhs rhs
   (GorbowNamedInternalProvability.augment (GorbowNamedInternalProvability.augment pF0 pCK) box) pR
   (CurrentQuantifierLogicalSource.selectedOld rawOld) a baseX))[peelTag]? = some ⟨3,RuntimeOffsetAugmentationProducer.program⟩)
 (hbaseProducer : (nodes (CumulativePropositionalSource.root f lhs rhs
   (GorbowNamedInternalProvability.augment (GorbowNamedInternalProvability.augment pF0 pCK) box) pR
   (CurrentQuantifierLogicalSource.selectedOld rawOld) a baseX))[baseTag]? = some ⟨2,CurrentStructuralProducerCompiler.compile pF0⟩)
 (hcheckerInventory : (nodes (CumulativePropositionalSource.root f lhs rhs
   (GorbowNamedInternalProvability.augment (GorbowNamedInternalProvability.augment pF0 pCK) box) pR
   (CurrentQuantifierLogicalSource.selectedOld rawOld) a baseX))[checkerInventoryTag]? =
  some ⟨6,CurrentStructuralProducerInventory.carrier f lhs rhs CurrentNamedHeaderCertificate.template (CurrentQuantifierLogicalSource.selectedOld rawOld) a baseX
   (CumulativePropositionalSource.verifier f lhs rhs (CurrentQuantifierLogicalSource.selectedOld rawOld) a baseX)⟩)
 (hcheckerProducer : (nodes (CumulativePropositionalSource.root f lhs rhs
   (GorbowNamedInternalProvability.augment (GorbowNamedInternalProvability.augment pF0 pCK) box) pR
   (CurrentQuantifierLogicalSource.selectedOld rawOld) a baseX))[checkerTag]? =
  some ⟨6,CurrentStructuralProducerCompiler.compile (CumulativePropositionalSource.verifier f lhs rhs (CurrentQuantifierLogicalSource.selectedOld rawOld) a baseX)⟩)
 (ht : (nodes (CumulativePropositionalSource.root f lhs rhs
   (GorbowNamedInternalProvability.augment (GorbowNamedInternalProvability.augment pF0 pCK) box) pR
   (CurrentQuantifierLogicalSource.selectedOld rawOld) a baseX))[transformTag]? = some ⟨3,CurrentExistentialIntroductionProgram.program⟩)
 (hp : (nodes (CumulativePropositionalSource.root f lhs rhs
   (GorbowNamedInternalProvability.augment (GorbowNamedInternalProvability.augment pF0 pCK) box) pR
   (CurrentQuantifierLogicalSource.selectedOld rawOld) a baseX))[publishedTag]? = some ⟨7,CurrentPublishedProvabilityIntroduction.program⟩) :
 let t := CurrentNamedHeaderCertificate.template
 let old := CurrentQuantifierLogicalSource.selectedOld rawOld
 let pF := GorbowNamedInternalProvability.augment (GorbowNamedInternalProvability.augment pF0 pCK) box
 let q := CumulativePropositionalSource.verifier f lhs rhs old a baseX
 let root := CumulativePropositionalSource.root f lhs rhs pF pR old a baseX
 let R := CurrentPublishedProvabilityIntroduction.RuntimeRebase.shared root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) I
 ∃ bound : Nat, ∀ (sigma : Sentence) ctx (innerFuel innerCert outerFuel : Term ctx),
 let K := tags R.previous
 let code := inputCode K R.previous.previous.current.constructorTag
  R.previous.previous.previous.previous.template.certificateTag pF0 pCK box q peelTag baseTag checkerTag pF c sigma innerFuel innerCert
 Nonempty (Derivation (S pF pR q)
  (.imp (orderGuard (Term.numeral bound) outerFuel)
   (.imp (CurrentCheckerSuccessCertificate.success pF c innerFuel (LiteralCheckerSuccessBridge.value pF c sigma) innerCert)
    (accepted R.currentK.coreTag R.currentK.verifierTag (Term.numeral (Encodable.encode c)) outerFuel
     (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode (.imp (rho pF c) (prD pF c sigma)))))
     (CurrentPublishedProvabilityIntroduction.outputCode publishedTag pF c sigma innerFuel innerCert code))))) := by
 let old := CurrentQuantifierLogicalSource.selectedOld rawOld
 let t := CurrentNamedHeaderCertificate.template
 let pF := GorbowNamedInternalProvability.augment (GorbowNamedInternalProvability.augment pF0 pCK) box
 let q := CumulativePropositionalSource.verifier f lhs rhs old a baseX
 let root := CumulativePropositionalSource.root f lhs rhs pF pR old a baseX
 let R := CurrentPublishedProvabilityIntroduction.RuntimeRebase.shared root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) I
 obtain ⟨bound,hinput⟩ := LiteralCheckerSuccessBridge.StatementChecks.exactSource f lhs rhs old a baseX pF0 pR pCK box c
  hA hbase I carrierTag peelTag baseTag checkerInventoryTag checkerTag hcarrier hpeel hbaseProducer hcheckerInventory hcheckerProducer
 have hpub := CurrentPublishedProvabilityIntroduction.SourceEndpoint.bridge f lhs rhs t rawOld a baseX pF pR c I N transformTag publishedTag ht hp
 refine ⟨bound,?_⟩
 intro sigma ctx innerFuel innerCert outerFuel
 let K := tags R.previous
 let code := inputCode K R.previous.previous.current.constructorTag
  R.previous.previous.previous.previous.template.certificateTag pF0 pCK box q peelTag baseTag checkerTag pF c sigma innerFuel innerCert
 let U := S pF pR q
 let guard := orderGuard (Term.numeral (n := ctx) bound) outerFuel
 let success := CurrentCheckerSuccessCertificate.success pF c innerFuel (LiteralCheckerSuccessBridge.value pF c sigma) innerCert
 let G := [success,guard]
 obtain ⟨hi⟩ := hinput sigma ctx innerFuel innerCert outerFuel
 obtain ⟨hp⟩ := hpub sigma ctx innerFuel innerCert code (Term.numeral (Encodable.encode c)) outerFuel
 have hg : Hilbert.Local U ctx G guard := .hypothesis (List.mem_cons_of_mem success List.mem_cons_self)
 have hs : Hilbert.Local U ctx G success := .hypothesis List.mem_cons_self
 have heq := Hilbert.Local.mp (.mp (.base hi) hg) hs
 have hout := Hilbert.Local.mp (.base hp) heq
 exact ⟨hout.discharge.discharge.finish⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourcePublishedWitness.SourceBridge
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourcePublishedWitness.SourceBridge
