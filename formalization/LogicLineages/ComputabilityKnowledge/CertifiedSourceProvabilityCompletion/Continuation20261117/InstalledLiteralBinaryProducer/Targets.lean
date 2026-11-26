module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence



open HistoryRuleSuffix

/-- Exact installed computation graph, with actual root and child ASTs. Offset
inputs are original second-child offsets; no computed output/certificate oracle. -/
def Graph : Prop :=
 ∀ (f : Formula 1) (lhs rhs : Term 1) (old a : Program 1) (baseX : Program 3)
 (pF0 pR : Program 1) (pCK : Program 2) (pG : Program 6),
 let t := CurrentNamedHeaderCertificate.template
 let pF := selected f lhs rhs old a baseX pF0 pCK pG
 let outer := CumulativePropositionalSource.verifier f lhs rhs old a baseX
 let root := CumulativePropositionalSource.root f lhs rhs pF pR old a baseX
 ∀ I : CumulativePropositionalSource.JointInstallation root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX),
 ∀ (peelTag baseProducerTag producerTag : Nat),
 (nodes root)[peelTag]? = some ⟨3,RuntimeOffsetAugmentationProducer.program⟩ →
 (nodes root)[baseProducerTag]? = some ⟨2,CurrentStructuralProducerCompiler.compile pF0⟩ →
 (nodes root)[producerTag]? = some ⟨5,program pF0⟩ →
 let R := CurrentPublishedProvabilityIntroduction.RuntimeRebase.shared root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) I
 ∀ ctx (r s : Term ctx),
 let K := tags R.previous
 let box := InstalledProducerExtra.container pG (extra f lhs rhs old a baseX pF0)
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory root)
  (.equal (call producerTag (inputs pF0 pCK box outer r s))
   (RetainedBaseLiteralBinary.certificate K R.previous.previous.current.constructorTag
    R.previous.previous.previous.previous.template.certificateTag pF0 pCK box outer peelTag baseProducerTag r s)))

/-- One NEW source selects its index only AFTER installing the literal producer.
Full original Retained/Packages and uniform acceptance share precisely that tuple. -/
def OneSource : Prop := ∀ (f : Formula 1) (lhs rhs : Term 1),
 ∃ (old a : Program 1) (baseX : Program 3) (offset : Nat),
 ∃ (pF0 pR : Program 1) (c : Code) (tagCK : Nat) (pCK : Program 2) (tagG : Nat) (pG : Program 6)
 (mtag xtag carrierTag peelTag baseProducerTag producerTag : Nat),
 let t := CurrentNamedHeaderCertificate.template
 let pF := selected f lhs rhs old a baseX pF0 pCK pG
 let outer := CumulativePropositionalSource.verifier f lhs rhs old a baseX
 let root := CumulativePropositionalSource.root f lhs rhs pF pR old a baseX
 ∃ I : CumulativePropositionalSource.JointInstallation root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX),
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
 (nodes root)[baseProducerTag]? = some ⟨2,CurrentStructuralProducerCompiler.compile pF0⟩ ∧
 (nodes root)[producerTag]? = some ⟨5,program pF0⟩ ∧
 let R := CurrentPublishedProvabilityIntroduction.RuntimeRebase.shared root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) I
 ∃ bound : Nat, ∀ ctx (r s fuel : Term ctx),
 let K := tags R.previous
 let U := S pF pR outer
 let box := InstalledProducerExtra.container pG (extra f lhs rhs old a baseX pF0)
 Nonempty (Derivation U (SixSol20261112.Fuel.orderGuard (Term.numeral bound) fuel)) →
 Nonempty (Derivation U
  (accepted R.currentK.coreTag R.currentK.verifierTag (Term.numeral (Encodable.encode c)) fuel
   (equalValue K.ctag K.atag (RetainedBaseLiteralBinary.rawBinary K r s)
    (LiteralNumeralPrefix.numeralCall K.numeralTag (GorbowBooleanTruth.binaryCodeTerm 0 r s)))
   (call producerTag (inputs pF0 pCK box outer r s))))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.Targets
