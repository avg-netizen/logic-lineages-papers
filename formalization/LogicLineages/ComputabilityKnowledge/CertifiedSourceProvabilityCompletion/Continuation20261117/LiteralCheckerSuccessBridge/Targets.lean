module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
/-- Actual same-source literal checker supplier, with original checker AST
inventory, not a pre-assumed successful certificate. Arbitrary box permits a
later common base-only inventory including quantifier and published-intro nodes.
The uniform bound precedes sigma, context, and both inner witnesses. -/
def Source : Prop :=
 ∀ (f : Formula 1) (lhs rhs : Term 1) (old a : Program 1) (baseX : Program 3)
 (pF0 pR : Program 1) (pCK : Program 2) (box : Program 6) (c : Code),
 let t := CurrentNamedHeaderCertificate.template
 let pF := GorbowNamedInternalProvability.augment (GorbowNamedInternalProvability.augment pF0 pCK) box
 let q := CumulativePropositionalSource.verifier f lhs rhs old a baseX
 let root := CumulativePropositionalSource.root f lhs rhs pF pR old a baseX
 Actual pF pR q c →
 (∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v) →
 ∀ I : CumulativePropositionalSource.JointInstallation root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX),
 ∀ (carrierTag peelTag baseProducerTag checkerInventoryTag checkerProducerTag : Nat),
 (nodes root)[carrierTag]? = some ⟨6,CurrentStructuralProducerInventory.carrier f lhs rhs t old a baseX pF0⟩ →
 (nodes root)[peelTag]? = some ⟨3,RuntimeOffsetAugmentationProducer.program⟩ →
 (nodes root)[baseProducerTag]? = some ⟨2,CurrentStructuralProducerCompiler.compile pF0⟩ →
 (nodes root)[checkerInventoryTag]? = some ⟨6,CurrentStructuralProducerInventory.carrier f lhs rhs t old a baseX q⟩ →
 (nodes root)[checkerProducerTag]? = some ⟨6,CurrentStructuralProducerCompiler.compile q⟩ →
 let R := CurrentPublishedProvabilityIntroduction.RuntimeRebase.shared root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) I
 ∃ bound : Nat, ∀ (sigma : Sentence) ctx (innerFuel innerCert outerFuel : Term ctx),
 let K := tags R.previous
 let r : Term ctx := Term.numeral (GorbowSortedSyntaxCode.formulaCode (rho pF c))
 let s : Term ctx := Term.numeral (GorbowSortedSyntaxCode.formulaCode sigma)
 let literalProof := RetainedBaseLiteralBinary.certificate K R.previous.previous.current.constructorTag
  R.previous.previous.previous.previous.template.certificateTag pF0 pCK box q peelTag baseProducerTag r s
 let checkerProof := CurrentCheckerSuccessCertificate.proofCode checkerProducerTag pF c innerFuel (value pF c sigma) innerCert
 Nonempty (Derivation (S pF pR q)
  (.imp (SixSol20261112.Fuel.orderGuard (Term.numeral bound) outerFuel)
   (.imp (CurrentCheckerSuccessCertificate.success pF c innerFuel (value pF c sigma) innerCert)
    (accepted R.currentK.coreTag R.currentK.verifierTag (Term.numeral (Encodable.encode c)) outerFuel
     (CurrentPublishedProvabilityIntroduction.checkerEquationCode K pF c sigma innerFuel innerCert)
     (certificate K pF c sigma innerFuel innerCert literalProof checkerProof)))))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.LiteralCheckerSuccessBridge.Targets
