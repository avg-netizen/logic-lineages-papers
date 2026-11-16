module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram.SyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram.NativeValues
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GorbowRegistryTuple PrescribedRuntimeEquality PrescribedRuntimeCallCongruence HistoryRuleSuffix
open HistoryRuleSuffix.NativeProof

theorem inputsEval {m : Nat} (target : Nat) (inputs : List.Vector Nat m) (i : Fin m) :
 evaluate ((inputPrograms m).get i) (target ::ᵥ inputs) = inputs.get i := by
 simp only [inputPrograms,List.Vector.get_ofFn,evaluate,List.Vector.get_cons_succ]

theorem inputVector {m : Nat} (target : Nat) (inputs : List.Vector Nat m) :
 (List.Vector.ofFn (fun i => evaluate ((inputPrograms m).get i) (target ::ᵥ inputs))) = inputs := by
 ext i
 simp only [List.Vector.get_ofFn,inputsEval]

theorem argumentEval {m n : Nat} (g : Fin n → Program m) (target : Nat) (inputs : List.Vector Nat m) (i : Fin n) :
 evaluate ((argumentValues g).get i) (target ::ᵥ inputs) = evaluate (g i) inputs := by
 simp only [argumentValues,List.Vector.get_ofFn,evaluate,inputVector]

theorem rawEval {m : Nat} (target : Nat) (inputs : List.Vector Nat m) (i : Fin m) :
 evaluate ((rawPrograms m).get i) (target ::ᵥ inputs) = Encodable.encode (GorbowTermPrefixCode.encode (Term.numeral (inputs.get i) : Term 0)) := by
 simp only [rawPrograms,List.Vector.get_map,oneEval,inputsEval]
 exact LiteralNumeralPrefix.StatementChecks.exactNative _

theorem childEval {m n : Nat} (f : Program n) (g : Fin n → Program m) (G : Fin n → Program (m+1))
 (target : Nat) (inputs : List.Vector Nat m) (i : Fin n) :
 evaluate ((argumentCodes f g G).get i) (target ::ᵥ inputs) = evaluate (G i) ((target+argumentTag f g i) ::ᵥ inputs) := by
 simp only [argumentCodes,List.Vector.get_ofFn,evaluate]
 congr 1
 ext j
 cases j using Fin.cases with
 | zero =>
  simpa only [List.Vector.get_ofFn,Fin.cases_zero,List.Vector.get_cons_zero,projectionEval] using
   CurrentRecursionStepProgram.NativeEvaluation.shiftEval (argumentTag f g i) (.projection 0) (target ::ᵥ inputs)
 | succ j => simp only [List.Vector.get_ofFn,Fin.cases_succ,List.Vector.get_cons_succ,inputsEval]

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram.NativeValues
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram.NativeValues
