module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeRules
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeQuotes
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeAssembly
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeLeaves
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeInstances
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open CurrentRecursionBaseProgram.NativePrimitives CurrentRecursionBaseProgram.TransitivityNativeProof
open HistoryRuleSuffix HistoryRuleSuffix.NativeProof PrescribedRuntimeEquality CurrentImplicationCertificate CurrentEqualityImplication
open NativeOperations NativeRules NativeQuotes

theorem leftInstance {m : Nat} (offset target counter : Nat) (inputs : List.Vector Nat m) :
 evaluate (termQuote (leftTemplate m offset) (CurrentRecursionBaseProgram.rootArguments (m+1))) (target ::ᵥ counter ::ᵥ inputs) =
 Encodable.encode (GorbowTermPrefixCode.encode (GorbowClosedEquality.instantiateTerm
  (CurrentRecursionStepCertificate.closedStepFunction (target+offset) counter inputs)
  (call target (Term.numeral counter ::ᵥ GorbowPRNumeralCalculation.numeralArguments inputs)))) := by
 rw [CurrentRecursionStepCertificate.TemplateTraceProof.instantiateStep]
 exact NativeLeaves.left offset target counter inputs

theorem rightInstance {m : Nat} (base : Program m) (step : Program (m+2)) (target counter : Nat) (inputs : List.Vector Nat m) :
 evaluate (termQuote (rightTemplate m (GorbowPRChildTags.stepTag base)) (rightArguments base step)) (target ::ᵥ counter ::ᵥ inputs) =
 Encodable.encode (GorbowTermPrefixCode.encode (GorbowClosedEquality.instantiateTerm
  (CurrentRecursionStepCertificate.closedStepFunction (target+GorbowPRChildTags.stepTag base) counter inputs)
  (Term.numeral (evaluate (.recursion base step) (counter ::ᵥ inputs))))) := by
 rw [CurrentRecursionStepCertificate.TemplateTraceProof.instantiateStep]
 exact rightQuote base step target counter inputs

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeInstances
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeInstances
