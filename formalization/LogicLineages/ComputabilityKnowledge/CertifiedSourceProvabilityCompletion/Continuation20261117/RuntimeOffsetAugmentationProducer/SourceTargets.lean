module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.CorrectedAugmentationErasure.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.SourceTargets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence HistoryRuleSuffix
open GorbowPublishedDCB
/-- Genuine same-source accepted call of the fixed runtime-offset producer.
A single bound precedes every augment/producer occurrence and runtime input.
Actual seed membership, constructor separation and raw validators are derived,
not supplied as success or tag-equality premises. This does not yet install the
producer into a newly selected source or compile a selected base dispatcher. -/
def InstalledSource : Prop :=
 ∀ (installed : Formula 1) (lhs rhs : Term 1) k (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code),
 Actual pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX) c →
 (∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v) →
 ∀ I : CumulativePropositionalSource.JointInstallation
  (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX),
 ∃ seedFuel : Nat, ∀ n (p : Program 1) (q : Program n) (tag producerTag : Nat),
 (nodes (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX))[tag]? =
  some ⟨1,GorbowNamedInternalProvability.augment p q⟩ →
 (nodes (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX))[producerTag]? =
  some ⟨3,program⟩ →
 ∀ ctx (value fuel : Term ctx),
 let K := tags I.previous
 let offset := argumentTag (.projection (0 : Fin 2)) (CorrectedAugmentationErasure.branches p q) 1
 Nonempty (Derivation (S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX))
  (.imp (SixSol20261112.Fuel.orderGuard (Term.numeral seedFuel) fuel)
   (accepted I.currentK.coreTag I.currentK.verifierTag (Term.numeral (Encodable.encode c)) fuel
    (equalValue K.ctag K.atag (CorrectedAugmentationErasure.left K tag value)
     (CorrectedAugmentationErasure.right K p q tag value))
    (call producerTag (Term.numeral tag ::ᵥ Term.numeral offset ::ᵥ value ::ᵥ nil)))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RuntimeOffsetAugmentationProducer.SourceTargets
