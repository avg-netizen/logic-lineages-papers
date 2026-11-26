module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalHB3.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalHB3.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
/-- Original HB3 at the SAME fresh source with full Retained/Packages and
all actual witness-supplier fields retained. This is an unpaid target, not a
claim that the accepted witness supplier already proves existential assembly. -/
def Source : Prop :=
∀ (f : Formula 1) (lhs rhs : Term 1),
 ∃ (rawOld a : Program 1) (baseX : Program 3) (offset : Nat)
 (pF0 pR : Program 1) (c : Code) (tagCK : Nat) (pCK : Program 2) (tagG : Nat) (pG : Program 6)
 (mtag xtag carrierTag peelTag baseTag checkerInventoryTag checkerTag literalTag publishedExtraTag transformTag publishedTag : Nat),
 let t := CurrentNamedHeaderCertificate.template
 let old := CurrentQuantifierLogicalSource.selectedOld rawOld
 let pF := selected f lhs rhs rawOld a baseX pF0 pCK pG
 let q := CumulativePropositionalSource.verifier f lhs rhs old a baseX
 let root := CumulativePropositionalSource.root f lhs rhs pF pR old a baseX
 let box := InstalledProducerExtra.container pG (extra f lhs rhs rawOld a baseX pF0)
 ∃ I : CumulativePropositionalSource.JointInstallation root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX),
 ∃ N : CurrentExistentialIntroductionProgram.LogicalInterface.Nodes root,
 (∀ v, evaluate rawOld v = HistoryDispatcher.logicalFunction v) ∧
 (∀ v, evaluate old v = HistoryDispatcher.logicalFunction v) ∧
 (∀ v, evaluate a v = HistoryDispatcher.arithmeticFunction v) ∧
 (∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v) ∧
 GorbowSelectedDistribution.Calibrated pF0 pR ∧
 LiteralValidatedSource.Retained (CumulativePropositionalSource.logical f lhs rhs old)
  (CumulativePropositionalSource.arithmetic a) (SaturatedAxiomLeaf.saturated baseX)
  offset pF pR c tagCK pCK tagG pG ∧
 CumulativePropositionalSource.Packages f lhs rhs old a baseX offset pF pR c mtag xtag ∧
 (nodes root)[mtag]? = some ⟨4,LiteralRawMP.constructor⟩ ∧
 (nodes root)[12]? = some ⟨1,pF0⟩ ∧
 (nodes root)[carrierTag]? = some ⟨6,CurrentStructuralProducerInventory.carrier f lhs rhs t old a baseX pF0⟩ ∧
 (nodes root)[peelTag]? = some ⟨3,RuntimeOffsetAugmentationProducer.program⟩ ∧
 (nodes root)[baseTag]? = some ⟨2,CurrentStructuralProducerCompiler.compile pF0⟩ ∧
 (nodes root)[checkerInventoryTag]? = some ⟨6,CurrentStructuralProducerInventory.carrier f lhs rhs t old a baseX q⟩ ∧
 (nodes root)[checkerTag]? = some ⟨6,CurrentStructuralProducerCompiler.compile q⟩ ∧
 (nodes root)[literalTag]? = some ⟨5,InstalledLiteralBinaryProducer.program pF0⟩ ∧
 (nodes root)[publishedExtraTag]? = some ⟨6,CurrentPublishedProvabilityIntroduction.extra f lhs rhs t rawOld a baseX⟩ ∧
 (nodes root)[transformTag]? = some ⟨3,CurrentExistentialIntroductionProgram.program⟩ ∧
 (nodes root)[publishedTag]? = some ⟨7,CurrentPublishedProvabilityIntroduction.program⟩ ∧
 (∀ sigma : Sentence, prD pF c sigma = .ex (.ex
  (CurrentPublishedProvabilityIntroduction.SyntaxSupport.checkerBody
   (GorbowNamedInternalProvability.checkerTag pF) (Encodable.encode c)
   (CurrentPublishedProvabilityIntroduction.PublishedSyntax.argument pF c sigma)))) ∧
 (∀ sigma : Sentence, Nonempty (Derivation (S pF pR q)
  (.equal (LiteralCheckerSuccessBridge.value (ctx := 0) pF c (prD pF c sigma))
   (.add (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode (.imp (rho pF c) (prD pF c sigma)))))
    (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode (.imp (rho pF c) (prD pF c sigma))))))))) ∧
 (let R := CurrentPublishedProvabilityIntroduction.RuntimeRebase.shared root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) I
 ∃ bound : Nat, ∀ (sigma : Sentence) ctx (innerFuel innerCert outerFuel : Term ctx),
 let K := tags R.previous
 let code := inputCode K R.previous.previous.current.constructorTag
  R.previous.previous.previous.previous.template.certificateTag pF0 pCK box q peelTag baseTag checkerTag pF c sigma innerFuel innerCert
 Nonempty (Derivation (S pF pR q)
  (.imp (SixSol20261112.Fuel.orderGuard (Term.numeral bound) outerFuel)
   (.imp (CurrentCheckerSuccessCertificate.success pF c innerFuel (LiteralCheckerSuccessBridge.value pF c sigma) innerCert)
    (accepted R.currentK.coreTag R.currentK.verifierTag (Term.numeral (Encodable.encode c)) outerFuel
     (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode (.imp (rho pF c) (prD pF c sigma)))))
     (CurrentPublishedProvabilityIntroduction.outputCode publishedTag pF c sigma innerFuel innerCert code)))))) ∧
 (∀ sigma : Sentence, Nonempty (Derivation (S pF pR q)
  (GorbowPublishedLobReduction.hb3 pF c sigma)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.SameSourceOriginalHB3.Targets
