module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.NativeUnary
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.NativeScalar
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof
open CurrentRecursionBaseProgram.GraphPrimitives
open CurrentRecursionBaseProgram.NativePrimitives CurrentRecursionBaseProgram.TransitivityNativeProof HistoryRuleSuffix.NativeProof

theorem unaryCode {arity : Nat} (opcode : Nat) (a : Program arity) (v : List.Vector Nat arity) (xs : List Nat)
 (ha : evaluate a v = Encodable.encode xs) :
 evaluate (FixedFormulaSubstitution.unary opcode a) v = Encodable.encode (opcode :: xs) := by
 simp only [FixedFormulaSubstitution.unary,twoEval,constantEval,ha,consEval,HistoryLookup.NativeProof.encodeCons]
 rfl

theorem operation {arity depth : Nat} (multiply : Bool) (a b : Program arity) (v : List.Vector Nat arity) (x y : Term depth)
 (ha : evaluate a v = Encodable.encode (GorbowTermPrefixCode.encode x))
 (hb : evaluate b v = Encodable.encode (GorbowTermPrefixCode.encode y)) :
 evaluate (FixedFormulaSubstitution.binary (if multiply then 4 else 3) a b) v =
 Encodable.encode (GorbowTermPrefixCode.encode (binaryTerm multiply x y)) := by
 cases multiply <;> exact binaryEval _ _ _ _ _ _ ha hb

theorem simple {arity : Nat} (universal : Bool) (t u code : Program arity) (v : List.Vector Nat arity) (a b : Term 0)
 (ht : evaluate t v = Encodable.encode (GorbowTermPrefixCode.encode a))
 (hu : evaluate u v = Encodable.encode (GorbowTermPrefixCode.encode b)) :
 evaluate (unaryClosed (if universal then .universalFunction (.var 0) else .succ (.var 0)) t u code) v =
 unaryNumber (if universal then .universalFunction (.var 0) else .succ (.var 0)) a b (evaluate code v) := by
 apply NativeUnary.ordinary
 · have h := NativeUnary.quoteTerm boundEnvironment
    (if universal then Term.universalFunction (.var 0) else .succ (.var 0)) nil v Fin.elim0 (fun i => Fin.elim0 i)
   cases universal <;> simpa [GorbowSubstitution.substitute,FixedFormulaSubstitution.assignment,boundEnvironment] using h
 · exact ht
 · exact hu
 · have h := NativeUnary.quoteTerm (UniformRuntimeEnvironmentAgreement.specialize boundEnvironment)
    (if universal then Term.universalFunction (.var 0) else .succ (.var 0)) (t ::ᵥ nil) v (fun _ : Fin 1 => a)
    (fun i => Fin.cases ht (fun j => Fin.elim0 j) i)
   rw [PrescribedRuntimeEquality.EncodingProof.assignmentSpecialized] at h
   exact h
 · have h := NativeUnary.quoteTerm (UniformRuntimeEnvironmentAgreement.specialize boundEnvironment)
    (if universal then Term.universalFunction (.var 0) else .succ (.var 0)) (u ::ᵥ nil) v (fun _ : Fin 1 => b)
    (fun i => Fin.cases hu (fun j => Fin.elim0 j) i)
   rw [PrescribedRuntimeEquality.EncodingProof.assignmentSpecialized] at h
   exact h

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.NativeScalar
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.NativeScalar
