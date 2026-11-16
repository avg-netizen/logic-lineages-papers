module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerInventory.CoverageProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerInventory.ExtractionProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
variable {arity k : Nat} (p : Program arity) (installed : Formula 1)
 (lhs rhs : Term 1) (t : Term k) (old a : Program 1) (baseX : Program 3)

theorem localNodes {n : Nat} (q : Program n) (carrierTag : Nat)
 (hc : (nodes p)[carrierTag]? = some ⟨6,carrier installed lhs rhs t old a baseX q⟩)
 {m : Nat} (u : Program m) (hu : Occurs ⟨m,u⟩ q) :
 ∀ entry ∈ localItems installed lhs rhs t old a baseX u,
 ∃ (tag : Nat), (nodes p)[tag]? = some entry := by
 have hall := ReflexivityInstalled.BundleProof.bundleInstallation
  (inventory installed lhs rhs t old a baseX q) arity p carrierTag hc
 intro entry he
 exact hall entry (CoverageProof.occurrence installed lhs rhs t old a baseX hu entry he)

theorem compiledNode {n : Nat} (q : Program n) (carrierTag : Nat)
 (hc : (nodes p)[carrierTag]? = some ⟨6,carrier installed lhs rhs t old a baseX q⟩)
 {m : Nat} (u : Program m) (hu : Occurs ⟨m,u⟩ q) :
 ∃ (tag : Nat), (nodes p)[tag]? = some ⟨m+1,CurrentStructuralProducerCompiler.compile u⟩ :=
 localNodes p installed lhs rhs t old a baseX q carrierTag hc u hu _
  (CoverageProof.compiled installed lhs rhs t old a baseX u)

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerInventory.ExtractionProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerInventory.ExtractionProof
