module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase12.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase12.NativeAtomsProof
open GorbowPRProgram SixSol20261113 List.Vector HistoryRuleSuffix.NativeProof
open UniformClosedCase13.NativeAtomsProof
theorem firstAt (f t u : List Nat) : evaluate firstArg (Encodable.encode [f,t,u] ::ᵥ nil) = Encodable.encode f :=
 HistoryLookup.NativeProof.headCons f [t,u]
theorem secondAt (f t u : List Nat) : evaluate secondArg (Encodable.encode [f,t,u] ::ᵥ nil) = Encodable.encode t := by
 rw [secondArg,oneEval,HistoryLookup.NativeProof.tailList]
 exact HistoryLookup.NativeProof.headCons t [u]
theorem thirdAt (f t u : List Nat) : evaluate thirdArg (Encodable.encode [f,t,u] ::ᵥ nil) = Encodable.encode u := by
 rw [thirdArg,oneEval,oneEval,HistoryLookup.NativeProof.tailList,HistoryLookup.NativeProof.tailList]
 exact HistoryLookup.NativeProof.headCons u []
theorem leftAt (f t u : List Nat) : evaluate leftInstance (Encodable.encode [f,t,u] ::ᵥ nil) =
 Encodable.encode (GorbowInstanceCode.instanceCode 0 f t) := by
 rw [leftInstance,twoEval,firstAt,secondAt]
 exact UniformClosedInstanceRecognizer.StatementChecks.exactOriginalInstance f t
theorem rightAt (f t u : List Nat) : evaluate rightInstance (Encodable.encode [f,t,u] ::ᵥ nil) =
 Encodable.encode (GorbowInstanceCode.instanceCode 0 f u) := by
 rw [rightInstance,twoEval,firstAt,thirdAt]
 exact UniformClosedInstanceRecognizer.StatementChecks.exactOriginalInstance f u
theorem leftResultAt (f t u result : List Nat) (hi : GorbowInstanceCode.instanceCode 0 f t = some result) :
 evaluate leftResult (Encodable.encode [f,t,u] ::ᵥ nil) = Encodable.encode result := by
 rw [leftResult,oneEval,leftAt,hi]
 change evaluate HistoryCodec.predecessor ((Encodable.encode result).succ ::ᵥ nil) = _
 rw [HistoryCodec.NativeProof.evaluatePredecessor,Nat.pred_succ]
theorem rightResultAt (f t u result : List Nat) (hi : GorbowInstanceCode.instanceCode 0 f u = some result) :
 evaluate rightResult (Encodable.encode [f,t,u] ::ᵥ nil) = Encodable.encode result := by
 rw [rightResult,oneEval,rightAt,hi]
 change evaluate HistoryCodec.predecessor ((Encodable.encode result).succ ::ᵥ nil) = _
 rw [HistoryCodec.NativeProof.evaluatePredecessor,Nat.pred_succ]
theorem equalityAt (f t u : List Nat) : evaluate equality (Encodable.encode [f,t,u] ::ᵥ nil) =
 Encodable.encode (GorbowCodeConstructors.binary 0 t u) := by
 rw [equality,twoEval,constantEval,twoEval,secondAt,thirdAt,appendList]
 exact consList 0 (t ++ u)
theorem consequentAt (f t u left right : List Nat)
 (hl : GorbowInstanceCode.instanceCode 0 f t = some left)
 (hr : GorbowInstanceCode.instanceCode 0 f u = some right) :
 evaluate consequent (Encodable.encode [f,t,u] ::ᵥ nil) =
 Encodable.encode (GorbowCodeConstructors.binary 7 left right) := by
 rw [consequent,twoEval,constantEval,twoEval,leftResultAt f t u left hl,rightResultAt f t u right hr,appendList]
 exact consList 7 (left ++ right)
theorem implicationAt (f t u left right : List Nat)
 (hl : GorbowInstanceCode.instanceCode 0 f t = some left)
 (hr : GorbowInstanceCode.instanceCode 0 f u = some right) :
 evaluate implication (Encodable.encode [f,t,u] ::ᵥ nil) =
 Encodable.encode (GorbowCodeConstructors.binary 7 (GorbowCodeConstructors.binary 0 t u)
  (GorbowCodeConstructors.binary 7 left right)) := by
 rw [implication,twoEval,constantEval,twoEval,equalityAt,consequentAt f t u left right hl hr,appendList]
 exact consList 7 (GorbowCodeConstructors.binary 0 t u ++ GorbowCodeConstructors.binary 7 left right)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase12.NativeAtomsProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase12.NativeAtomsProof
