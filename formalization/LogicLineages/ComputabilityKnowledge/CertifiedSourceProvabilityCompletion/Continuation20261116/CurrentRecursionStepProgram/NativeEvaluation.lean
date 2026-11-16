module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.RuntimeSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeEvaluation
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open CurrentRecursionBaseProgram.NativePrimitives CurrentRecursionBaseProgram.TransitivityNativeProof
open HistoryRuleSuffix.NativeProof PrescribedRuntimeEquality CurrentImplicationCertificate CurrentEqualityImplication

theorem shiftEval {arity : Nat} (offset : Nat) (q : Program arity) (v : List.Vector Nat arity) :
 evaluate (shiftProgram offset q) v = evaluate q v + offset := by
 induction offset with
 | zero => rfl
 | succ n ih =>
  change (evaluate (shiftProgram n q) v).succ = evaluate q v + (n+1)
  rw [ih]
  rfl

theorem previousEval {m : Nat} (base : Program m) (step : Program (m+2)) (target counter : Nat) (inputs : List.Vector Nat m) :
 evaluate (previous base step) (target ::ᵥ counter ::ᵥ inputs) = evaluate (.recursion base step) (counter ::ᵥ inputs) :=
 CurrentCalculationFormulaProgram.NativeProof.tailEval _ target _

theorem stepArgsEval {m : Nat} (base : Program m) (step : Program (m+2)) (target counter : Nat) (inputs : List.Vector Nat m) :
 (List.Vector.ofFn fun i => evaluate (stepArguments base step i) (target ::ᵥ counter ::ᵥ inputs)) =
 counter ::ᵥ evaluate (.recursion base step) (counter ::ᵥ inputs) ::ᵥ inputs := by
 ext i
 cases i using Fin.cases with
 | zero => rfl
 | succ i => cases i using Fin.cases with
   | zero => exact previousEval base step target counter inputs
   | succ i => simp [stepArguments,evaluate]

theorem resultEval {m : Nat} (base : Program m) (step : Program (m+2)) (target counter : Nat) (inputs : List.Vector Nat m) :
 evaluate (result base step) (target ::ᵥ counter ::ᵥ inputs) =
 evaluate step (counter ::ᵥ evaluate (.recursion base step) (counter ::ᵥ inputs) ::ᵥ inputs) := by
 change evaluate step _ = _
 rw [stepArgsEval]

theorem childEval {m : Nat} (base : Program m) (step : Program (m+2)) (child : Program (m+3)) (target counter : Nat) (inputs : List.Vector Nat m) :
 evaluate (.composition child (childArguments base step)) (target ::ᵥ counter ::ᵥ inputs) =
 evaluate child ((target+GorbowPRChildTags.stepTag base) ::ᵥ counter ::ᵥ evaluate (.recursion base step) (counter ::ᵥ inputs) ::ᵥ inputs) := by
 change evaluate child _ = _
 congr 1
 ext i
 cases i using Fin.cases with
 | zero => simpa only [List.Vector.get_ofFn,childArguments,Fin.cases_zero,projectionEval,List.Vector.get_cons_zero] using shiftEval (GorbowPRChildTags.stepTag base) (.projection 0) (target ::ᵥ counter ::ᵥ inputs)
 | succ i =>
  have he := congrArg (fun v => v.get i) (stepArgsEval base step target counter inputs)
  simpa only [List.Vector.get_ofFn,childArguments,Fin.cases_succ,List.Vector.get_cons_succ] using he

theorem rightArgsEval {m : Nat} (base : Program m) (step : Program (m+2)) (target counter : Nat) (inputs : List.Vector Nat m) (i : Fin (m+3)) :
 evaluate (rightArguments base step i) (target ::ᵥ counter ::ᵥ inputs) =
 Encodable.encode (GorbowTermPrefixCode.encode (CurrentRecursionBaseProgram.TagSyntax.join target
  (fun j => Term.numeral ((counter ::ᵥ evaluate (.recursion base step) (counter ::ᵥ inputs) ::ᵥ inputs).get j)) i)) := by
 refine Fin.lastCases ?_ (fun j => ?_) i
 · simp only [rightArguments,Fin.lastCases_last,CurrentRecursionBaseProgram.TagSyntax.join,oneEval,projectionEval,List.Vector.get_cons_zero]
   exact LiteralNumeralPrefix.StatementChecks.exactNative target
 · simp only [rightArguments,Fin.lastCases_castSucc,CurrentRecursionBaseProgram.TagSyntax.join]
   cases j using Fin.cases with
   | zero => exact LiteralNumeralPrefix.StatementChecks.exactNative counter
   | succ j => cases j using Fin.cases with
     | zero =>
      simp only [Fin.cases_succ,Fin.cases_zero,oneEval,previousEval,List.Vector.get_cons_succ,List.Vector.get_cons_zero]
      exact LiteralNumeralPrefix.StatementChecks.exactNative _
     | succ j =>
      simp only [Fin.cases_succ,oneEval,projectionEval,List.Vector.get_cons_succ]
      exact LiteralNumeralPrefix.StatementChecks.exactNative _
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeEvaluation
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeEvaluation
