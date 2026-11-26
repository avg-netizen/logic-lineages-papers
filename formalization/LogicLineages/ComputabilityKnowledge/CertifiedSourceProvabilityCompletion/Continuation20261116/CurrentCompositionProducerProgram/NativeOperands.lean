module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram.NativeValues
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram.CallEncoding
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram.NativeOperands
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GorbowRegistryTuple PrescribedRuntimeEquality PrescribedRuntimeCallCongruence HistoryRuleSuffix
open HistoryRuleSuffix.NativeProof

theorem valueVector {m n : Nat} (g : Fin n → Program m) (target : Nat) (inputs : List.Vector Nat m) :
 (List.Vector.ofFn (fun i => evaluate ((argumentValues g).get i) (target ::ᵥ inputs))) =
 List.Vector.ofFn (fun i => evaluate (g i) inputs) := by
 ext i
 simp only [List.Vector.get_ofFn,NativeValues.argumentEval]

theorem result {m n : Nat} (f : Program n) (g : Fin n → Program m) (target : Nat) (inputs : List.Vector Nat m) :
 evaluate (.composition f (argumentValues g).get) (target ::ᵥ inputs) = evaluate f (List.Vector.ofFn (fun i => evaluate (g i) inputs)) := by
 change evaluate f _ = _
 rw [valueVector]

theorem functionCode {m n : Nat} (g : Fin n → Program m) (F : Program (n+1)) (target : Nat) (inputs : List.Vector Nat m) :
 evaluate (.composition F (Fin.cases (applyOne .succ (.projection 0)) (argumentValues g).get)) (target ::ᵥ inputs) =
 evaluate F ((target+1) ::ᵥ List.Vector.ofFn (fun i => evaluate (g i) inputs)) := by
 change evaluate F _ = _
 congr 1
 ext i
 cases i using Fin.cases with
 | zero => rfl
 | succ i => simp only [List.Vector.get_ofFn,Fin.cases_succ,List.Vector.get_cons_succ,NativeValues.argumentEval]

theorem rawValue {m n : Nat} (g : Fin n → Program m) (target : Nat) (inputs : List.Vector Nat m) (i : Fin n) :
 evaluate (((argumentValues g).map (applyOne LiteralNumeralPrefix.numeralCode)).get i) (target ::ᵥ inputs) =
 Encodable.encode (GorbowTermPrefixCode.encode (Term.numeral (evaluate (g i) inputs) : Term 0)) := by
 rw [List.Vector.get_map,oneEval,NativeValues.argumentEval,LiteralNumeralPrefix.StatementChecks.exactNative]

theorem quotedArgument {m n : Nat} (f : Program n) (g : Fin n → Program m) (target : Nat) (inputs : List.Vector Nat m) (i : Fin n) :
 evaluate ((argumentCalls f g).get i) (target ::ᵥ inputs) =
 Encodable.encode (GorbowTermPrefixCode.encode (call (target+argumentTag f g i) (GorbowPRNumeralCalculation.numeralArguments inputs))) := by
 simp only [argumentCalls,List.Vector.get_ofFn]
 apply CallEncoding.native _ _ _ _ _
  (CurrentRecursionStepProgram.NativeEvaluation.shiftEval (argumentTag f g i) (.projection 0) (target ::ᵥ inputs))
 intro j
 simpa only [GorbowPRNumeralCalculation.numeralArguments,List.Vector.get_map] using NativeValues.rawEval target inputs j

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram.NativeOperands
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram.NativeOperands
