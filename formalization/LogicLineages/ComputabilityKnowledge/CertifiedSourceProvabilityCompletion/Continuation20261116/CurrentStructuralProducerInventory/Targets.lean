module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerInventory.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerInventory.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
/-- One explicit carrier membership, not a coverage oracle, realizes existing
constructor interfaces at every original subtree and EVERY supplied occurrence.
This does not assert the carrier is in a newly selected published source. -/
def ConstructorInstallations : Prop :=
 ∀ arity (p : Program arity) (installed : Formula 1) (lhs rhs : Term 1) k (t : Term k)
 (old a : Program 1) (baseX : Program 3),
 CumulativePropositionalSource.JointInstallation p installed lhs rhs t old a
  (SaturatedAxiomLeaf.saturated baseX) →
 ∀ n (q : Program n) (carrierTag : Nat),
 (nodes p)[carrierTag]? = some ⟨6,carrier installed lhs rhs t old a baseX q⟩ →
 ∀ m (u : Program m), Occurs ⟨m,u⟩ q → ∀ (target : Nat),
 (nodes p)[target]? = some ⟨m,u⟩ →
 ∃ (producerTag : Nat),
 (nodes p)[producerTag]? = some ⟨m+1,CurrentStructuralProducerCompiler.compile u⟩ ∧
 InstalledAt p installed lhs rhs t old a baseX target producerTag u
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerInventory.Targets
