module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeRules
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeQuotes
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeAssembly
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeSeed
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open CurrentRecursionBaseProgram.NativePrimitives CurrentRecursionBaseProgram.TransitivityNativeProof
open HistoryRuleSuffix HistoryRuleSuffix.NativeProof PrescribedRuntimeEquality CurrentImplicationCertificate CurrentEqualityImplication
open NativeOperations NativeRules NativeQuotes

theorem seed {m : Nat} (base : Program m) (target counter : Nat) (inputs : List.Vector Nat m) :
 evaluate (CurrentRecursionBaseProgram.seedProgram (m+1) (rootTemplate m (GorbowPRChildTags.stepTag base))
  (CurrentRecursionBaseProgram.rootArguments (m+1))) (target ::ᵥ counter ::ᵥ inputs) =
 PrescribedRuntimeSpecialization.produce (CurrentRecursionStepCertificate.rootFormula base target)
  (Fin.cases (Term.numeral counter) (fun i => Term.numeral (inputs.get i)))
  (PrescribedSourceAxiomSpecialization.seed (CurrentRecursionStepCertificate.rootFormula base target)) := by
 have h := CurrentRecursionBaseProgram.SeedNativeProof.seed (target ::ᵥ counter ::ᵥ inputs) target (m+1)
  (rootTemplate m (GorbowPRChildTags.stepTag base)) (CurrentRecursionBaseProgram.rootArguments (m+1))
  (fun i => Term.numeral ((counter ::ᵥ inputs).get i))
  (CurrentRecursionBaseProgram.NativeInputs.rootArgumentsEval (m+1) target (counter ::ᵥ inputs))
 rw [TemplateSyntax.rootPlug] at h
 have he : (fun i : Fin (m+1) => (Term.numeral ((counter ::ᵥ inputs).get i) : Term 0)) =
  Fin.cases (Term.numeral counter) (fun i => Term.numeral (inputs.get i)) := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => rfl
 rw [he] at h
 exact h

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeSeed
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeSeed
