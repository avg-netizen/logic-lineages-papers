module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerInventory.PrimitiveProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerInventory.CompositionProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerInventory.RecursionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerInventory.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
theorem exactInstallations : Targets.ConstructorInstallations := by
 intro arity p installed lhs rhs k t old a baseX I n q carrierTag hc m u hu target htarget
 cases u with
 | zero =>
  obtain ⟨tag,htag⟩ := ExtractionProof.compiledNode p installed lhs rhs t old a baseX q carrierTag hc .zero hu
  exact ⟨tag,htag,PrimitiveProof.leaf p installed lhs rhs t old a _ I⟩
 | succ =>
  obtain ⟨tag,htag⟩ := ExtractionProof.compiledNode p installed lhs rhs t old a baseX q carrierTag hc .succ hu
  exact ⟨tag,htag,PrimitiveProof.leaf p installed lhs rhs t old a _ I⟩
 | projection i =>
  obtain ⟨tag,htag⟩ := ExtractionProof.compiledNode p installed lhs rhs t old a baseX q carrierTag hc (.projection i) hu
  exact ⟨tag,htag,PrimitiveProof.leaf p installed lhs rhs t old a _ I⟩
 | composition f g =>
  obtain ⟨tag,htag⟩ := ExtractionProof.compiledNode p installed lhs rhs t old a baseX q carrierTag hc (.composition f g) hu
  exact ⟨tag,htag,CompositionProof.installed p installed lhs rhs t old a baseX I q carrierTag hc f g hu target tag htarget⟩
 | recursion f g =>
  exact RecursionProof.installed p installed lhs rhs t old a baseX I q carrierTag hc f g hu target htarget

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerInventory.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerInventory.Proof
