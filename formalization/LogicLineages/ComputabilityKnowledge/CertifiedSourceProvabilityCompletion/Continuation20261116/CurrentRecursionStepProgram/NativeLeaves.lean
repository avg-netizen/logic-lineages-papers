module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeRules
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeQuotes
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeAssembly
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeLeaves
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open CurrentRecursionBaseProgram.NativePrimitives CurrentRecursionBaseProgram.TransitivityNativeProof
open HistoryRuleSuffix HistoryRuleSuffix.NativeProof PrescribedRuntimeEquality CurrentImplicationCertificate CurrentEqualityImplication
open NativeOperations NativeRules NativeQuotes

theorem prior {m : Nat} (target counter : Nat) (inputs : List.Vector Nat m) :
 evaluate (termQuote (priorTemplate m) (CurrentRecursionBaseProgram.rootArguments (m+1))) (target ::ᵥ counter ::ᵥ inputs) =
 Encodable.encode (GorbowTermPrefixCode.encode (call target (Term.numeral counter ::ᵥ GorbowPRNumeralCalculation.numeralArguments inputs))) := by
 have h := rootQuote (priorTemplate m) target counter inputs
 rw [RuntimeSyntax.priorClosed] at h
 exact h

theorem next {m : Nat} (target counter : Nat) (inputs : List.Vector Nat m) :
 evaluate (termQuote (nextTemplate m) (CurrentRecursionBaseProgram.rootArguments (m+1))) (target ::ᵥ counter ::ᵥ inputs) =
 Encodable.encode (GorbowTermPrefixCode.encode (call target (Term.numeral (counter+1) ::ᵥ GorbowPRNumeralCalculation.numeralArguments inputs))) := by
 have h := rootQuote (nextTemplate m) target counter inputs
 rw [RuntimeSyntax.nextClosed] at h
 exact h

theorem left {m : Nat} (offset target counter : Nat) (inputs : List.Vector Nat m) :
 evaluate (termQuote (leftTemplate m offset) (CurrentRecursionBaseProgram.rootArguments (m+1))) (target ::ᵥ counter ::ᵥ inputs) =
 Encodable.encode (GorbowTermPrefixCode.encode (call (target+offset) (Term.numeral counter ::ᵥ
  call target (Term.numeral counter ::ᵥ GorbowPRNumeralCalculation.numeralArguments inputs) ::ᵥ GorbowPRNumeralCalculation.numeralArguments inputs))) := by
 have h := rootQuote (leftTemplate m offset) target counter inputs
 rw [RuntimeSyntax.leftClosed] at h
 exact h

theorem previousNumeral {m : Nat} (base : Program m) (step : Program (m+2)) (target counter : Nat) (inputs : List.Vector Nat m) :
 evaluate (applyOne LiteralNumeralPrefix.numeralCode (previous base step)) (target ::ᵥ counter ::ᵥ inputs) =
 Encodable.encode (GorbowTermPrefixCode.encode (Term.numeral (evaluate (.recursion base step) (counter ::ᵥ inputs)) : Term 0)) := by
 rw [oneEval,NativeEvaluation.previousEval,LiteralNumeralPrefix.StatementChecks.exactNative]

theorem outputNumeral {m : Nat} (base : Program m) (step : Program (m+2)) (target counter : Nat) (inputs : List.Vector Nat m) :
 evaluate (applyOne LiteralNumeralPrefix.numeralCode (result base step)) (target ::ᵥ counter ::ᵥ inputs) =
 Encodable.encode (GorbowTermPrefixCode.encode (Term.numeral (evaluate step (counter ::ᵥ evaluate (.recursion base step) (counter ::ᵥ inputs) ::ᵥ inputs)) : Term 0)) := by
 rw [oneEval,NativeEvaluation.resultEval,LiteralNumeralPrefix.StatementChecks.exactNative]

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeLeaves
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeLeaves
