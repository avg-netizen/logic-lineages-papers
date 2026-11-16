module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram.NativeValues
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram.SeedNative
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GorbowRegistryTuple PrescribedRuntimeEquality PrescribedRuntimeCallCongruence HistoryRuleSuffix
open HistoryRuleSuffix.NativeProof

theorem seed {m n : Nat} (f : Program n) (g : Fin n → Program m) (target : Nat) (inputs : List.Vector Nat m) :
 evaluate (CurrentRecursionBaseProgram.seedProgram m (rootTemplate f g) (CurrentRecursionBaseProgram.rootArguments m)) (target ::ᵥ inputs) =
 PrescribedRuntimeSpecialization.produce (CurrentCompositionCertificate.rootFormula f g target)
  (fun i => Term.numeral (inputs.get i)) (PrescribedSourceAxiomSpecialization.seed (CurrentCompositionCertificate.rootFormula f g target)) := by
 have h := CurrentRecursionBaseProgram.SeedNativeProof.seed (target ::ᵥ inputs) target m (rootTemplate f g)
  (CurrentRecursionBaseProgram.rootArguments m) (fun i => Term.numeral (inputs.get i))
  (CurrentRecursionBaseProgram.NativeInputs.rootArgumentsEval m target inputs)
 rw [SyntaxProof.root] at h
 exact h

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram.SeedNative
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram.SeedNative
