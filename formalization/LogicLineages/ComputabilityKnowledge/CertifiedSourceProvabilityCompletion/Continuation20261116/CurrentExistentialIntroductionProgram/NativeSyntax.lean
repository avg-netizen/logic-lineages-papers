module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.NativeSyntax
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector HistoryRuleSuffix
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open HistoryRuleSuffix.NativeProof
theorem negEval {arity ctx : Nat} (a : Program arity) (v : List.Vector Nat arity) (A : Formula ctx)
 (ha : evaluate a v = Encodable.encode (GorbowFormulaPrefixCode.encode A)) :
 evaluate (neg a) v = Encodable.encode (GorbowFormulaPrefixCode.encode A.neg) :=
 OriginalQuantifierLogicalProducers.NativeSupport.unaryAt 6 a v (GorbowFormulaPrefixCode.encode A) ha

theorem allEval {arity ctx : Nat} (a : Program arity) (v : List.Vector Nat arity) (A : Formula (ctx+1))
 (ha : evaluate a v = Encodable.encode (GorbowFormulaPrefixCode.encode A)) :
 evaluate (allCode a) v = Encodable.encode (GorbowFormulaPrefixCode.encode A.all) :=
 OriginalQuantifierLogicalProducers.NativeSupport.unaryAt 10 a v (GorbowFormulaPrefixCode.encode A) ha

theorem exEval {arity ctx : Nat} (a : Program arity) (v : List.Vector Nat arity) (A : Formula (ctx+1))
 (ha : evaluate a v = Encodable.encode (GorbowFormulaPrefixCode.encode A)) :
 evaluate (exCode a) v = Encodable.encode (GorbowFormulaPrefixCode.encode A.ex) :=
 OriginalQuantifierLogicalProducers.NativeSupport.unaryAt 11 a v (GorbowFormulaPrefixCode.encode A) ha

theorem classicalEval {arity : Nat} (a b : Program arity) (v : List.Vector Nat arity) (A B : Formula 0)
 (ha : evaluate a v = Encodable.encode (GorbowFormulaPrefixCode.encode A))
 (hb : evaluate b v = Encodable.encode (GorbowFormulaPrefixCode.encode B)) :
 evaluate (logicalSingleton false a b) v = logicalNumber (.classicalContraposition A B) := by
 change evaluate (OriginalQuantifierLogicalProducers.singletonConstructor false) (evaluate a v ::ᵥ evaluate b v ::ᵥ nil) = _
 rw [ha,hb]
 exact (OriginalQuantifierLogicalProducers.StatementChecks.exactNative.1 A B).2

theorem existentialEval {arity : Nat} (a b : Program arity) (v : List.Vector Nat arity) (A : Formula 1)
 (ha : evaluate a v = Encodable.encode (GorbowFormulaPrefixCode.encode A)) :
 evaluate (logicalSingleton true a b) v = logicalNumber (.existsDualBackward A) := by
 change evaluate (OriginalQuantifierLogicalProducers.singletonConstructor true) (evaluate a v ::ᵥ evaluate b v ::ᵥ nil) = _
 rw [ha]
 exact (OriginalQuantifierLogicalProducers.StatementChecks.exactNative.2 A (evaluate b v)).2

theorem instanceEval {arity : Nat} (a witness : Program arity) (v : List.Vector Nat arity) (A : Formula 1) (t : Term 0)
 (ha : evaluate a v = Encodable.encode (GorbowFormulaPrefixCode.encode A))
 (ht : evaluate witness v = Encodable.encode (GorbowTermPrefixCode.encode t)) :
 evaluate (instantiateCode a witness) v = Encodable.encode (GorbowFormulaPrefixCode.encode (GorbowStandardInstances.instantiate A t)) := by
 have hi := (GorbowInstanceCodeProof.exactInstance 0 (GorbowFormulaPrefixCode.encode A)
  (GorbowTermPrefixCode.encode t) (GorbowFormulaPrefixCode.encode (GorbowStandardInstances.instantiate A t))).mpr
   ⟨A,t,rfl,rfl,rfl⟩
 rw [instantiateCode,oneEval,twoEval,ha,ht,UniformClosedInstanceRecognizer.StatementChecks.exactOriginalInstance,hi,
  HistoryCodec.NativeProof.evaluatePredecessor]
 rfl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.NativeSyntax
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.NativeSyntax
