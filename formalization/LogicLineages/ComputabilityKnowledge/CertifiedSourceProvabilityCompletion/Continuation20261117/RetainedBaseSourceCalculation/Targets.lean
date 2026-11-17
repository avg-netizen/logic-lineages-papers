module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseSourceCalculation.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseSourceCalculation.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence

/-- Actual selected source-function calculation through its retained primitive
base. Installation premises are the concrete node facts supplied by the checked
noncircular installer, not semantic compiler or certificate-success oracles.
The single object-language fuel guard is the same form as original SourceCore. -/
def SourceCalculation : Prop :=
 ∀ (f : Formula 1) (lhs rhs : Term 1) k (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF0 pR : Program 1) (pCK : Program 2) (pG : Program 6) (c : Code),
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
 ∃ bound : Nat, ∀ ctx (value fuel : Term ctx),
 let K := tags I.previous
 let U := S pF pR outer
 let box := InstalledProducerExtra.container pG (RetainedBaseProducerInstallation.extra f lhs rhs t old a baseX pF0)
 Nonempty (Derivation U (SixSol20261112.Fuel.orderGuard (Term.numeral bound) fuel)) →
 Nonempty (Derivation U
  (accepted I.currentK.coreTag I.currentK.verifierTag (Term.numeral (Encodable.encode c)) fuel
   (CurrentStructuralProducerCore.calculation K 6 (value ::ᵥ nil))
   (certificate K pF0 pCK box outer peelTag baseProducerTag value)))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseSourceCalculation.Targets
