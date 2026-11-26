module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentAugmentationErasure.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentAugmentationErasure.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeCallCongruence PrescribedRuntimeEquality
/-- Actual same-source current CORE/Fuel erasure at every installed augment.
No computation certificate, raw validator, or computed-result equation is a premise.
This is a constructor helper, not yet an installed producer or literal transport. -/
def InternalErasure : Prop :=
 ∀ (installed : Formula 1) (lhs rhs : Term 1) k (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code),
 Actual pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX) c →
 (∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v) →
 ∀ I : CumulativePropositionalSource.JointInstallation
  (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX),
 ∃ seedFuel : Nat, ∀ n (p : Program 1) (q : Program n) tag,
 (nodes (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX))[tag]? =
  some ⟨1,GorbowNamedInternalProvability.augment p q⟩ →
 ∀ ctx (input fuel : Term ctx),
 let K := tags I.previous
 Nonempty (Derivation (S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX))
  (.imp (SixSol20261112.Fuel.orderGuard (Term.numeral seedFuel) fuel)
   (accepted I.currentK.coreTag I.currentK.verifierTag (Term.numeral (Encodable.encode c)) fuel
    (equalValue K.ctag K.atag (left K tag input) (right K p q tag input))
    (certificate K p q tag input))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentAugmentationErasure.Targets
