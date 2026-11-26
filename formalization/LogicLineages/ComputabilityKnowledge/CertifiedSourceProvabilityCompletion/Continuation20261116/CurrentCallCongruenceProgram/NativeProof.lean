module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.NativeCall
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.InputProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.NativeProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof
open CurrentRecursionBaseProgram.GraphPrimitives
open HistoryRuleSuffix.NativeProof

theorem tailEval {arity : Nat} (q : Program arity) (target : Nat) (args : List.Vector Nat arity) :
 evaluate (tailProgram q) (target ::ᵥ args) = evaluate q args := by
 change evaluate q (List.Vector.ofFn fun i => (target ::ᵥ args).get i.succ) = _
 congr 1
 ext i
 simp only [List.Vector.get_ofFn,List.Vector.get_cons_succ]

theorem left {n : Nat} (xs ys : List.Vector (Term 0) n) (codes : List.Vector Nat n) (i : Fin n) :
 evaluate ((leftInputs n).get i) (pack (encodeTerms xs) (encodeTerms ys) codes) =
 Encodable.encode (GorbowTermPrefixCode.encode (xs.get i)) := by
 simp only [leftInputs,List.Vector.get_ofFn,evaluate,InputProof.left,encodeTerms,List.Vector.get_map]

theorem right {n : Nat} (xs ys : List.Vector (Term 0) n) (codes : List.Vector Nat n) (i : Fin n) :
 evaluate ((rightInputs n).get i) (pack (encodeTerms xs) (encodeTerms ys) codes) =
 Encodable.encode (GorbowTermPrefixCode.encode (ys.get i)) := by
 simp only [rightInputs,List.Vector.get_ofFn,evaluate,InputProof.right,encodeTerms,List.Vector.get_map]

theorem code {n : Nat} (xs ys : List.Vector (Term 0) n) (codes : List.Vector Nat n) (i : Fin n) :
 evaluate ((codeInputs n).get i) (pack (encodeTerms xs) (encodeTerms ys) codes) = codes.get i := by
 simp only [codeInputs,List.Vector.get_ofFn,evaluate,InputProof.code]

theorem exactTuple : Targets.NativeTuple := by
 intro n xs ys codes
 exact NativeTuple.certificate (leftInputs n) (rightInputs n) (codeInputs n) _ xs ys codes
  (left xs ys codes) (right xs ys codes) (code xs ys codes)

theorem exactCall : Targets.NativeCall := by
 intro n tag xs ys codes
 apply NativeCall.certificate (.projection 0) ((leftInputs n).map tailProgram)
  ((rightInputs n).map tailProgram) ((codeInputs n).map tailProgram)
  (tag ::ᵥ pack (encodeTerms xs) (encodeTerms ys) codes) tag xs ys codes
 · rfl
 · intro i
   rw [List.Vector.get_map,tailEval]
   exact left xs ys codes i
 · intro i
   rw [List.Vector.get_map,tailEval]
   exact right xs ys codes i
 · intro i
   rw [List.Vector.get_map,tailEval]
   exact code xs ys codes i

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.NativeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.NativeProof
