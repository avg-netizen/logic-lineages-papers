module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeRules
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeQuotes
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open CurrentRecursionBaseProgram.NativePrimitives CurrentRecursionBaseProgram.TransitivityNativeProof
open HistoryRuleSuffix HistoryRuleSuffix.NativeProof PrescribedRuntimeEquality CurrentImplicationCertificate CurrentEqualityImplication
open NativeOperations NativeRules NativeQuotes

theorem exactNative : Targets.NativeStep := by
 intro m base step child target counter inputs
 dsimp only
 let v := target ::ᵥ counter ::ᵥ inputs
 let d := GorbowPRChildTags.stepTag base
 let av := GorbowPRNumeralCalculation.numeralArguments inputs
 let prev := evaluate (.recursion base step) (counter ::ᵥ inputs)
 let out := evaluate step (counter ::ᵥ prev ::ᵥ inputs)
 let pc := call target (Term.numeral counter ::ᵥ av)
 let pn := (Term.numeral prev : Term 0)
 let nc := call target (Term.numeral (counter+1) ::ᵥ av)
 let l := call (target+d) (Term.numeral counter ::ᵥ pc ::ᵥ av)
 let r := call (target+d) (Term.numeral counter ::ᵥ pn ::ᵥ av)
 let o := (Term.numeral out : Term 0)
 let raws := CurrentRecursionBaseProgram.rootArguments (m+1)
 have hpc := rootQuote (priorTemplate m) target counter inputs
 rw [RuntimeSyntax.priorClosed] at hpc
 have hnc := rootQuote (nextTemplate m) target counter inputs
 rw [RuntimeSyntax.nextClosed] at hnc
 have hl := rootQuote (leftTemplate m d) target counter inputs
 rw [RuntimeSyntax.leftClosed] at hl
 have hr := rightQuote base step target counter inputs
 have hp : evaluate (applyOne LiteralNumeralPrefix.numeralCode (previous base step)) v = Encodable.encode (GorbowTermPrefixCode.encode pn) := by
  rw [oneEval,NativeEvaluation.previousEval,LiteralNumeralPrefix.StatementChecks.exactNative]
 have ho : evaluate (applyOne LiteralNumeralPrefix.numeralCode (result base step)) v = Encodable.encode (GorbowTermPrefixCode.encode o) := by
  rw [oneEval,NativeEvaluation.resultEval,LiteralNumeralPrefix.StatementChecks.exactNative]
 have hP := equalEval _ _ v pc pn hpc hp
 have hroot := equalEval _ _ v nc l hnc hl
 have hchild := equalEval _ _ v r o hr ho
 have hseed := CurrentRecursionBaseProgram.SeedNativeProof.seed v target (m+1) (rootTemplate m d) raws
  (fun i => Term.numeral ((counter ::ᵥ inputs).get i))
  (CurrentRecursionBaseProgram.NativeInputs.rootArgumentsEval (m+1) target (counter ::ᵥ inputs))
 rw [TemplateSyntax.rootPlug] at hseed
 let f := CurrentRecursionStepCertificate.closedStepFunction (target+d) counter inputs
 have hl' : evaluate (termQuote (leftTemplate m d) raws) v = Encodable.encode (GorbowTermPrefixCode.encode (GorbowClosedEquality.instantiateTerm f pc)) := by
  rw [CurrentRecursionStepCertificate.TemplateTraceProof.instantiateStep]
  exact hl
 have hr' : evaluate (termQuote (rightTemplate m d) (rightArguments base step)) v = Encodable.encode (GorbowTermPrefixCode.encode (GorbowClosedEquality.instantiateTerm f pn)) := by
  rw [CurrentRecursionStepCertificate.TemplateTraceProof.instantiateStep]
  exact hr
 unfold program
 rw [NativeRules.transitivityEval _ _ _ _ _ _ v (.equal pc pn) nc r o hP hnc hr ho]
 rw [NativeRules.transitivityEval _ _ _ _ _ _ v (.equal pc pn) nc l r hP hnc hl hr]
 rw [liftEval _ _ _ v _ _ hroot hP,hseed]
 rw [unaryEval _ _ _ _ _ v f pc pn (unaryQuote m d target counter inputs) hpc hp hl' hr']
 rw [liftEval _ _ _ v _ _ hchild hP,NativeEvaluation.childEval]
 rfl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeProof
