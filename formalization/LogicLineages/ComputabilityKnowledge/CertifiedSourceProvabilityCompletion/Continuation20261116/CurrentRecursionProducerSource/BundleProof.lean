module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerSource.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerSource.BundleProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
theorem unpack {arity k m : Nat} (p : Program arity) (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (base : Program m) (step : Program (m+2))
 (B : Program (m+1)) (G : Program (m+3)) (extraTag : Nat)
 (he : (nodes p)[extraTag]? = some ⟨6,extendedExtra installed lhs rhs t old a baseX base step B G⟩) :
 ∃ oldExtraTag carrierTag : Nat,
 (nodes p)[oldExtraTag]? = some ⟨6,CumulativePropositionalSource.extra installed lhs rhs t old a baseX⟩ ∧
 (nodes p)[carrierTag]? = some ⟨6,producerCarrier base step B G⟩ ∧
 (∀ q ∈ producerItems base step B G, ∃ (tag : Nat), (nodes p)[tag]? = some q) := by
 have hall := ReflexivityInstalled.BundleProof.bundleInstallation
  [⟨6,CumulativePropositionalSource.extra installed lhs rhs t old a baseX⟩,⟨6,producerCarrier base step B G⟩] arity p extraTag he
 obtain ⟨oldExtraTag,ho⟩ := hall ⟨6,CumulativePropositionalSource.extra installed lhs rhs t old a baseX⟩ (by simp)
 obtain ⟨carrierTag,hc⟩ := hall ⟨6,producerCarrier base step B G⟩ (by simp)
 exact ⟨oldExtraTag,carrierTag,ho,hc,ReflexivityInstalled.BundleProof.bundleInstallation (producerItems base step B G) arity p carrierTag hc⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerSource.BundleProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerSource.BundleProof
