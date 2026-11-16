module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerSource.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerSource.BundleProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
theorem unpack {arity k n : Nat} (p : Program arity) (f : Formula 1)
 (lhs rhs : Term 1) (t : Term k) (Q : Program 1 → Program 1 → Program 3 → Program n)
 (old a : Program 1) (baseX : Program 3) (extraTag : Nat)
 (he : (nodes p)[extraTag]? = some ⟨6,extendedExtra f lhs rhs t Q old a baseX⟩) :
 ∃ (oldExtraTag inventoryTag : Nat),
 (nodes p)[oldExtraTag]? = some ⟨6,CumulativePropositionalSource.extra f lhs rhs t old a baseX⟩ ∧
 (nodes p)[inventoryTag]? = some ⟨6,CurrentStructuralProducerInventory.carrier f lhs rhs t old a baseX (Q old a baseX)⟩ := by
 have hall := ReflexivityInstalled.BundleProof.bundleInstallation
  [⟨6,CumulativePropositionalSource.extra f lhs rhs t old a baseX⟩,
   ⟨6,CurrentStructuralProducerInventory.carrier f lhs rhs t old a baseX (Q old a baseX)⟩] arity p extraTag he
 obtain ⟨oldExtraTag,ho⟩ := hall ⟨6,CumulativePropositionalSource.extra f lhs rhs t old a baseX⟩ (by simp)
 obtain ⟨inventoryTag,hi⟩ := hall ⟨6,CurrentStructuralProducerInventory.carrier f lhs rhs t old a baseX (Q old a baseX)⟩ (by simp)
 exact ⟨oldExtraTag,inventoryTag,ho,hi⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerSource.BundleProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerSource.BundleProof
