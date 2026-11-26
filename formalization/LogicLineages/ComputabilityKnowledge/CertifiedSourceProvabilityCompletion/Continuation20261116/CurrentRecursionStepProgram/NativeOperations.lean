module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeOperations
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open CurrentRecursionBaseProgram.NativePrimitives CurrentRecursionBaseProgram.TransitivityNativeProof
open HistoryRuleSuffix.NativeProof PrescribedRuntimeEquality CurrentImplicationCertificate CurrentEqualityImplication

theorem propositionalEval {arity : Nat} (isS : Bool) (a b c : Program arity) (v : List.Vector Nat arity)
 (A B C : Formula 0)
 (ha : evaluate a v = Encodable.encode (GorbowFormulaPrefixCode.encode A))
 (hb : evaluate b v = Encodable.encode (GorbowFormulaPrefixCode.encode B))
 (hc : evaluate c v = Encodable.encode (GorbowFormulaPrefixCode.encode C)) :
 evaluate (propositional isS a b c) v = UniformClosedPropositional.singletonNumber isS A B C := by
 apply singletonEval
 change evaluate (UniformClosedPropositional.lineConstructor isS) (evaluate a v ::ᵥ evaluate b v ::ᵥ evaluate c v ::ᵥ nil) = _
 rw [ha,hb,hc,UniformClosedPropositional.StatementChecks.exactNativeLine,CurrentImplicationCertificate.SingletonTraceProof.nativeLine]

theorem liftEval {arity : Nat} (a b code : Program arity) (v : List.Vector Nat arity) (A B : Formula 0)
 (ha : evaluate a v = Encodable.encode (GorbowFormulaPrefixCode.encode A))
 (hb : evaluate b v = Encodable.encode (GorbowFormulaPrefixCode.encode B)) :
 evaluate (liftProgram a b code) v = liftNumber A B (evaluate code v) := by
 unfold liftProgram
 rw [mpEval _ _ _ v _ (impEval b a v B A hb ha),propositionalEval _ _ _ _ v A B A ha hb ha]
 rfl

theorem mpUnderEval {arity : Nat} (p q r hi ha : Program arity) (v : List.Vector Nat arity) (P Q R : Formula 0)
 (hp : evaluate p v = Encodable.encode (GorbowFormulaPrefixCode.encode P))
 (hq : evaluate q v = Encodable.encode (GorbowFormulaPrefixCode.encode Q))
 (hr : evaluate r v = Encodable.encode (GorbowFormulaPrefixCode.encode R)) :
 evaluate (mpUnderProgram p q r hi ha) v = mpUnderNumber P Q R (evaluate hi v) (evaluate ha v) := by
 unfold mpUnderProgram
 rw [mpEval _ _ _ v _ (impEval p r v P R hp hr)]
 rw [mpEval _ _ _ v _ (impEval _ _ v _ _ (impEval p q v P Q hp hq) (impEval p r v P R hp hr))]
 rw [propositionalEval _ _ _ _ v P Q R hp hq hr]
 rfl

theorem reflexivityEval {arity : Nat} (raw : Program arity) (v : List.Vector Nat arity) (t : Term 0)
 (ht : evaluate raw v = Encodable.encode (GorbowTermPrefixCode.encode t)) :
 evaluate (reflexivity raw) v = GorbowNumericCertificate.certificateNumber [GorbowProofChecker.logicalLine (.reflexive t)] := by
 apply singletonEval
 rw [oneEval,ht,RawReflexivity.StatementChecks.exactNativeLine]
 rfl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeOperations
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeOperations
