module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase13.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase13.NativeAtomsProof
open GorbowPRProgram SixSol20261113 List.Vector HistoryRuleSuffix.NativeProof
/-- Original nested-list argument decoder, not a trace/history codec. -/
theorem firstAt (f t : List Nat) : evaluate firstArg (Encodable.encode [f,t] ::ᵥ nil) = Encodable.encode f :=
 HistoryLookup.NativeProof.headCons f [t]
theorem secondAt (f t : List Nat) : evaluate secondArg (Encodable.encode [f,t] ::ᵥ nil) = Encodable.encode t := by
 rw [secondArg,oneEval,HistoryLookup.NativeProof.tailList]
 exact HistoryLookup.NativeProof.headCons t []
theorem instanceAt (f t : List Nat) : evaluate instantiated (Encodable.encode [f,t] ::ᵥ nil) =
 Encodable.encode (GorbowInstanceCode.instanceCode 0 f t) := by
 rw [instantiated,twoEval,firstAt,secondAt]
 exact UniformClosedInstanceRecognizer.StatementChecks.exactOriginalInstance f t
theorem consList (a : Nat) (xs : List Nat) :
 evaluate HistoryCodec.cons (a ::ᵥ Encodable.encode xs ::ᵥ nil) = Encodable.encode (a::xs) := by
 rw [HistoryCodec.NativeProof.nativeConsAllVectors]
 rfl
theorem quantifiedAt (f t : List Nat) : evaluate quantified (Encodable.encode [f,t] ::ᵥ nil) =
 Encodable.encode (GorbowCodeConstructors.unary 10 f) := by
 rw [quantified,twoEval,constantEval,firstAt]
 exact consList 10 f
theorem resultAt (f t result : List Nat) (hi : GorbowInstanceCode.instanceCode 0 f t = some result) :
 evaluate instanceResult (Encodable.encode [f,t] ::ᵥ nil) = Encodable.encode result := by
 rw [instanceResult,oneEval,instanceAt,hi]
 change evaluate HistoryCodec.predecessor ((Encodable.encode result).succ ::ᵥ nil) = _
 rw [HistoryCodec.NativeProof.evaluatePredecessor,Nat.pred_succ]
theorem implicationAt (f t result : List Nat) (hi : GorbowInstanceCode.instanceCode 0 f t = some result) :
 evaluate implication (Encodable.encode [f,t] ::ᵥ nil) =
 Encodable.encode (GorbowCodeConstructors.binary 7 (GorbowCodeConstructors.unary 10 f) result) := by
 rw [implication,twoEval,constantEval,twoEval,quantifiedAt,resultAt f t result hi,appendList]
 exact consList 7 (GorbowCodeConstructors.unary 10 f ++ result)
theorem noneCode : Encodable.encode (none : Option (List Nat)) = 0 := rfl
theorem someCode (xs : List Nat) : Encodable.encode (some xs) = (Encodable.encode xs).succ := rfl
theorem successorEval (a : Nat) : evaluate .succ (a ::ᵥ nil) = a.succ := rfl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase13.NativeAtomsProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase13.NativeAtomsProof
