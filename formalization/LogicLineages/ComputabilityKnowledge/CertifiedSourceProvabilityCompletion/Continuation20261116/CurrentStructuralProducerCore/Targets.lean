module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
/-- One fixed-I bound before ALL program, inventory, subtree, occurrence and
runtime choices. Actual compiled ASTs only; no child correctness premises.
The antecedent is an object-language arithmetic guard derivation, not a
meta-level fuel inequality. Every IH must retain this same source/index/fuel. -/
def SourceCore : Prop :=
 ∀ (installed : Formula 1) (lhs rhs : Term 1) k (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code),
 Actual pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX) c →
 (∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v) →
 ∀ I : CumulativePropositionalSource.JointInstallation
  (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX),
 ∃ bound : Nat, ∀ n (q : Program n) (inventoryTag : Nat),
 (nodes (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX))[inventoryTag]? =
  some ⟨6,CurrentStructuralProducerInventory.carrier installed lhs rhs t old a baseX q⟩ →
 ∀ m (u : Program m), Occurs ⟨m,u⟩ q → ∀ (target producerTag : Nat),
 (nodes (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX))[target]? = some ⟨m,u⟩ →
 (nodes (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX))[producerTag]? =
  some ⟨m+1,CurrentStructuralProducerCompiler.compile u⟩ →
 ∀ ctx (inputs : List.Vector (Term ctx) m) (fuel : Term ctx),
 let U := S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX)
 let J := tags I.previous
 let index : Term ctx := Term.numeral (Encodable.encode c)
 Nonempty (Derivation U (SixSol20261112.Fuel.orderGuard (Term.numeral bound) fuel)) →
 Nonempty (Derivation U
  (accepted I.currentK.coreTag I.currentK.verifierTag index fuel
   (calculation J target inputs) (code producerTag target inputs)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.Targets
