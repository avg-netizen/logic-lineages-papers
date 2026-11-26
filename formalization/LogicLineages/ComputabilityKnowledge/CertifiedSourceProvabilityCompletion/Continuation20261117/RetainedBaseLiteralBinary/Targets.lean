module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseLiteralBinary.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseLiteralBinary.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence


/-- Same noncircular selected source, now specialized at the actual arithmetic
header template so its compiler occurrence is derived from I, not a new oracle.
Original literal binaryCodeTerm occurs on BOTH sides of the code/value bridge.
No alias-producer or header-transport-producer node premise is introduced. -/
def LiteralCalculation : Prop :=
 ∀ (f : Formula 1) (lhs rhs : Term 1) (old a : Program 1) (baseX : Program 3)
 (pF0 pR : Program 1) (pCK : Program 2) (pG : Program 6) (c : Code),
 let t := CurrentNamedHeaderCertificate.template
 let pF := RetainedBaseProducerInstallation.selected f lhs rhs t old a baseX pF0 pCK pG
 let outer := CumulativePropositionalSource.verifier f lhs rhs old a baseX
 let root := CumulativePropositionalSource.root f lhs rhs pF pR old a baseX
 Actual pF pR outer c →
 (∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v) →
 ∀ I : CumulativePropositionalSource.JointInstallation root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX),
 ∀ (carrierTag peelTag baseProducerTag : Nat),
 (nodes root)[carrierTag]? = some ⟨6,CurrentStructuralProducerInventory.carrier f lhs rhs t old a baseX pF0⟩ →
 (nodes root)[peelTag]? = some ⟨3,RuntimeOffsetAugmentationProducer.program⟩ →
 (nodes root)[baseProducerTag]? = some ⟨2,CurrentStructuralProducerCompiler.compile pF0⟩ →
 let R := CurrentPublishedProvabilityIntroduction.RuntimeRebase.shared root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) I
 ∃ bound : Nat, ∀ ctx (r s fuel : Term ctx),
 let K := tags R.previous
 let U := S pF pR outer
 let box := InstalledProducerExtra.container pG (RetainedBaseProducerInstallation.extra f lhs rhs t old a baseX pF0)
 Nonempty (Derivation U (SixSol20261112.Fuel.orderGuard (Term.numeral bound) fuel)) →
 Nonempty (Derivation U
  (accepted R.currentK.coreTag R.currentK.verifierTag (Term.numeral (Encodable.encode c)) fuel
   (equalValue K.ctag K.atag (rawBinary K r s)
    (LiteralNumeralPrefix.numeralCall K.numeralTag (GorbowBooleanTruth.binaryCodeTerm 0 r s)))
   (certificate K R.previous.previous.current.constructorTag
    R.previous.previous.previous.previous.template.certificateTag pF0 pCK box outer peelTag baseProducerTag r s)))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseLiteralBinary.Targets
