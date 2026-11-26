module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerSource.BundleProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerSource.InventoryProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
theorem rootPrograms {arity k n : Nat} (p : Program arity) (f : Formula 1)
 (lhs rhs : Term 1) (t : Term k) (old a : Program 1) (baseX : Program 3)
 (q : Program n) (inventoryTag : Nat)
 (hi : (nodes p)[inventoryTag]? = some ⟨6,CurrentStructuralProducerInventory.carrier f lhs rhs t old a baseX q⟩) :
 ∃ (evaluatorTag producerTag : Nat),
 (nodes p)[evaluatorTag]? = some ⟨n,q⟩ ∧
 (nodes p)[producerTag]? = some ⟨n+1,CurrentStructuralProducerCompiler.compile q⟩ := by
 have hall := CurrentStructuralProducerInventory.ExtractionProof.localNodes p f lhs rhs t old a baseX
  q inventoryTag hi q (.here q rfl)
 obtain ⟨evaluatorTag,hq⟩ := hall _ (CurrentStructuralProducerInventory.CoverageProof.evaluator f lhs rhs t old a baseX q)
 obtain ⟨producerTag,hC⟩ := hall _ (CurrentStructuralProducerInventory.CoverageProof.compiled f lhs rhs t old a baseX q)
 exact ⟨evaluatorTag,producerTag,hq,hC⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerSource.InventoryProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerSource.InventoryProof
