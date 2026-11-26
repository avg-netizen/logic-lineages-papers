module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerInventory.AnchoredRecursion
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerInventory.RecursionProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
theorem installed {arity k n m : Nat} (p : Program arity) (installed : Formula 1)
 (lhs rhs : Term 1) (t : Term k) (old a : Program 1) (baseX : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX))
 (q : Program n) (carrierTag : Nat)
 (hc : (nodes p)[carrierTag]? = some ⟨6,carrier installed lhs rhs t old a baseX q⟩)
 (f : Program m) (g : Program (m+2)) (hu : Occurs ⟨m+1,.recursion f g⟩ q)
 (target : Nat) (hq : (nodes p)[target]? = some ⟨m+1,.recursion f g⟩) :
 ∃ (producerTag : Nat),
 (nodes p)[producerTag]? = some ⟨m+2,CurrentStructuralProducerCompiler.compile (.recursion f g)⟩ ∧
 InstalledAt p installed lhs rhs t old a baseX target producerTag (.recursion f g) := by
 obtain ⟨extraTag,he⟩ := ExtractionProof.localNodes p installed lhs rhs t old a baseX q carrierTag hc
  (.recursion f g) hu _ (CoverageProof.extended installed lhs rhs t old a baseX f g)
 obtain ⟨oldExtraTag,localCarrierTag,ho,hcarrier,hall⟩ :=
  CurrentRecursionProducerSource.BundleProof.unpack p installed lhs rhs t old a baseX f g
   (CurrentStructuralProducerCompiler.compile f) (CurrentStructuralProducerCompiler.compile g) extraTag he
 obtain ⟨R,hR⟩ := AnchoredRecursion.installed p installed lhs rhs t old a baseX I f g
  (CurrentStructuralProducerCompiler.compile f) (CurrentStructuralProducerCompiler.compile g)
  extraTag oldExtraTag localCarrierTag he ho hcarrier hall target hq
 exact ⟨R.producer.publicTag,R.producer.hpublic,R,hR,rfl⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerInventory.RecursionProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerInventory.RecursionProof
