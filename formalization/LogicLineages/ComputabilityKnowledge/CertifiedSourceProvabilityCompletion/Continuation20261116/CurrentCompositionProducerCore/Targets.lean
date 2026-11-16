module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
/-- One original fixed-I seed bound, before all composition programs, node
addresses and runtime parameters. The only runtime logical inputs are its fuel
guard and original structural child CORE IHs. Actual source membership supplies
all defining equations; duplicate evaluator/code occurrence coherence and
transport to the original I recipe must be proved, never assumed. -/
def SourceCore : Prop :=
 ∀ (installed : Formula 1) (lhs rhs : Term 1) k (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code),
 Actual pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX) c →
 (∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v) →
 ∀ I : CumulativePropositionalSource.JointInstallation
  (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX),
 ∃ seedFuel : Nat, ∀ m n (f : Program n) (g : Fin n → Program m)
 (F : Program (n+1)) (G : Fin n → Program (m+1)) (J : CurrentCompositionProducerProgram.Tags n)
 (target producerTag : Nat),
 CurrentCompositionProducerProgram.Installation
  (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX) f g F G J →
 (nodes (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX))[target]? =
  some ⟨m,Program.composition f g⟩ →
 (nodes (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX))[producerTag]? =
  some ⟨m+1,CurrentCompositionProducerProgram.program f g F G⟩ →
 ∀ ctx (assumptions : List (Formula ctx)) (inputs : List.Vector (Term ctx) m) (fuel : Term ctx),
 let U := S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX)
 let K := tags I.previous
 let index : Term ctx := Term.numeral (Encodable.encode c)
 let values := childValues f g target inputs
 Nonempty (Hilbert.Local U ctx assumptions (SixSol20261112.Fuel.orderGuard (Term.numeral seedFuel) fuel)) →
 (∀ i, Nonempty (Hilbert.Local U ctx assumptions
  (core I.currentK.coreTag index fuel (calculation K (target+argumentTag f g i) inputs)
   (producerCode (J.argumentProducerTags i) (target+argumentTag f g i) inputs)))) →
 Nonempty (Hilbert.Local U ctx assumptions
  (core I.currentK.coreTag index fuel (calculation K (target+1) values)
   (producerCode J.functionProducerTag (target+1) values))) →
 Nonempty (Hilbert.Local U ctx assumptions
  (accepted I.currentK.coreTag I.currentK.verifierTag index fuel
   (calculation K target inputs) (producerCode producerTag target inputs)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerCore.Targets
