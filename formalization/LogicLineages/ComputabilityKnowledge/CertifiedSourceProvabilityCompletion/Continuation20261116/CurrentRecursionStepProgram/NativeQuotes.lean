module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeEvaluation
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeQuotes
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open CurrentRecursionBaseProgram.NativePrimitives CurrentRecursionBaseProgram.TransitivityNativeProof
open HistoryRuleSuffix.NativeProof PrescribedRuntimeEquality CurrentImplicationCertificate CurrentEqualityImplication
open GorbowSubstitution GorbowFormulaSubstitution

theorem rootQuote {m : Nat} (t : Term (m+2)) (target counter : Nat) (inputs : List.Vector Nat m) :
 evaluate (termQuote t (CurrentRecursionBaseProgram.rootArguments (m+1))) (target ::ᵥ counter ::ᵥ inputs) =
 Encodable.encode (GorbowTermPrefixCode.encode (substitute (CurrentRecursionBaseProgram.TagSyntax.join target
  (fun i => Term.numeral ((counter ::ᵥ inputs).get i))) t)) :=
 CurrentRecursionBaseProgram.NativeInputs.quoteTerms t _ _ _ (CurrentRecursionBaseProgram.NativeInputs.rootArgumentsEval (m+1) target (counter ::ᵥ inputs))

theorem rightQuote {m : Nat} (base : Program m) (step : Program (m+2)) (target counter : Nat) (inputs : List.Vector Nat m) :
 evaluate (termQuote (rightTemplate m (GorbowPRChildTags.stepTag base)) (rightArguments base step)) (target ::ᵥ counter ::ᵥ inputs) =
 Encodable.encode (GorbowTermPrefixCode.encode (call (target+GorbowPRChildTags.stepTag base)
  (Term.numeral counter ::ᵥ Term.numeral (evaluate (.recursion base step) (counter ::ᵥ inputs)) ::ᵥ GorbowPRNumeralCalculation.numeralArguments inputs))) := by
 unfold termQuote
 rw [CurrentRecursionBaseProgram.NativeInputs.quoteTerms _ _ _ _ (NativeEvaluation.rightArgsEval base step target counter inputs),RuntimeSyntax.rightClosed]

theorem liftNumeral (k : Nat) : renameTerm (Fin.succ : Fin 0 → Fin 1) (Term.numeral k) = Term.numeral k :=
 GorbowHeaderSubstitutionProof.numerals 0 1 _ k

theorem openAssigned (m offset target counter : Nat) (inputs : List.Vector Nat m) :
 substitute (liftSubstitute (CurrentRecursionBaseProgram.TagSyntax.join target (fun i => Term.numeral ((counter ::ᵥ inputs).get i)))) (unaryTemplate m offset) =
 CurrentRecursionStepCertificate.closedStepFunction (target+offset) counter inputs := by
 rw [RuntimeSyntax.head,RuntimeSyntax.unaryPlug]
 have he : liftSubstitute (fun i => (Term.numeral ((counter ::ᵥ inputs).get i) : Term 0)) =
  CurrentRecursionStepCertificate.TemplateTraceProof.assignment counter inputs := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => cases i using Fin.cases with
    | zero => exact liftNumeral counter
    | succ i =>
     simp only [liftSubstitute,Fin.cases_succ,List.Vector.get_cons_succ,CurrentRecursionStepCertificate.TemplateTraceProof.assignment,
      liftNumeral,GorbowClosedEquality.liftClosedTerm,SixSol20261112.Fuel.Logic.substNumeral]
 rw [he,CurrentRecursionStepCertificate.TemplateTraceProof.assigned]

theorem unaryQuote (m offset target counter : Nat) (inputs : List.Vector Nat m) :
 evaluate (unaryCode m offset) (target ::ᵥ counter ::ᵥ inputs) =
 Encodable.encode (GorbowTermPrefixCode.encode (CurrentRecursionStepCertificate.closedStepFunction (target+offset) counter inputs)) := by
 let sigma := CurrentRecursionBaseProgram.TagSyntax.join target (fun i => (Term.numeral ((counter ::ᵥ inputs).get i) : Term 0))
 have hv : (List.Vector.ofFn fun i => evaluate (CurrentRecursionBaseProgram.rootArguments (m+1) i) (target ::ᵥ counter ::ᵥ inputs)) =
  FixedFormulaSubstitution.rawInputs sigma := by
  ext i
  simpa only [FixedFormulaSubstitution.rawInputs,List.Vector.get_ofFn,sigma] using
   CurrentRecursionBaseProgram.NativeInputs.rootArgumentsEval (m+1) target (counter ::ᵥ inputs) i
 change evaluate (FixedFormulaSubstitution.termProgram _ _) _ = _
 rw [hv,FixedFormulaSubstitution.StatementChecks.exactNativeTerm,PrescribedRuntimeSpecialization.TraceSupportProof.assignmentHead]
 rw [openAssigned]
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeQuotes
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeQuotes
