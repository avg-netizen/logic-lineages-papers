module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.NativeScalar
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.NativeSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.NativeBinary
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof
open CurrentRecursionBaseProgram.GraphPrimitives
open CurrentRecursionBaseProgram.NativePrimitives CurrentRecursionBaseProgram.TransitivityNativeProof HistoryRuleSuffix.NativeProof

theorem coordinate {arity : Nat} (multiply right : Bool) (closed t u code : Program arity) (v : List.Vector Nat arity)
 (a b c : Term 0)
 (ha : evaluate closed v = Encodable.encode (GorbowTermPrefixCode.encode a))
 (hb : evaluate t v = Encodable.encode (GorbowTermPrefixCode.encode b))
 (hc : evaluate u v = Encodable.encode (GorbowTermPrefixCode.encode c)) :
 evaluate (CurrentCallCongruenceProgram.unary binaryEnvironment
  (if right then binaryTerm multiply (.var 1) (.var 0) else binaryTerm multiply (.var 0) (.var 1))
  (closed ::ᵥ nil) t u code) v =
 unaryNumber (if right then binaryTerm multiply (GorbowClosedEquality.liftClosedTerm 1 a) (.var 0)
  else binaryTerm multiply (.var 0) (GorbowClosedEquality.liftClosedTerm 1 a)) b c (evaluate code v) := by
 apply NativeUnary.ordinary
 · have h := NativeUnary.quoteTerm binaryEnvironment (if right then binaryTerm multiply (.var 1) (.var 0) else binaryTerm multiply (.var 0) (.var 1)) (closed ::ᵥ nil) v (fun _ : Fin 1 => a)
    (fun i => Fin.cases ha (fun j => Fin.elim0 j) i)
   rw [NativeSyntax.openBinary] at h
   exact h
 · exact hb
 · exact hc
 · have h := NativeUnary.quoteTerm (UniformRuntimeEnvironmentAgreement.specialize binaryEnvironment) (if right then binaryTerm multiply (.var 1) (.var 0) else binaryTerm multiply (.var 0) (.var 1)) (t ::ᵥ closed ::ᵥ nil) v
    (Fin.cases b (fun _ : Fin 1 => a)) (fun i => Fin.cases hb (fun j => Fin.cases ha (fun k => Fin.elim0 k) j) i)
   rw [NativeSyntax.closedBinary] at h
   cases right <;> simp only [Bool.false_eq_true,ite_false,ite_true,
    PrescribedRuntimeCallCongruence.ScalarTraceProof.instantiateLeft,PrescribedRuntimeCallCongruence.ScalarTraceProof.instantiateRight] <;> exact h
 · have h := NativeUnary.quoteTerm (UniformRuntimeEnvironmentAgreement.specialize binaryEnvironment) (if right then binaryTerm multiply (.var 1) (.var 0) else binaryTerm multiply (.var 0) (.var 1)) (u ::ᵥ closed ::ᵥ nil) v
    (Fin.cases c (fun _ : Fin 1 => a)) (fun i => Fin.cases hc (fun j => Fin.cases ha (fun k => Fin.elim0 k) j) i)
   rw [NativeSyntax.closedBinary] at h
   cases right <;> simp only [Bool.false_eq_true,ite_false,ite_true,
    PrescribedRuntimeCallCongruence.ScalarTraceProof.instantiateLeft,PrescribedRuntimeCallCongruence.ScalarTraceProof.instantiateRight] <;> exact h

theorem binaryEval {arity : Nat} (multiply : Bool) (a b c d hac hbd : Program arity) (v : List.Vector Nat arity)
 (av bv cv dv : Term 0)
 (ha : evaluate a v = Encodable.encode (GorbowTermPrefixCode.encode av))
 (hb : evaluate b v = Encodable.encode (GorbowTermPrefixCode.encode bv))
 (hc : evaluate c v = Encodable.encode (GorbowTermPrefixCode.encode cv))
 (hd : evaluate d v = Encodable.encode (GorbowTermPrefixCode.encode dv)) :
 evaluate (CurrentCallCongruenceProgram.binary multiply a b c d hac hbd) v = binaryNumber multiply av bv cv dv (evaluate hac v) (evaluate hbd v) := by
 unfold CurrentCallCongruenceProgram.binary
 rw [CurrentRecursionBaseProgram.TransitivityNativeProof.transitivityEval _ _ _ _ _ v _ _ _
  (NativeScalar.operation multiply a b v av bv ha hb)
  (NativeScalar.operation multiply c b v cv bv hc hb)
  (NativeScalar.operation multiply c d v cv dv hc hd)]
 rw [coordinate multiply false b a c hac v bv av cv hb ha hc,coordinate multiply true c b d hbd v cv bv dv hc hb hd]
 rfl

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.NativeBinary
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCallCongruenceProgram.NativeBinary
