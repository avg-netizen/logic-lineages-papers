module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit.NativeAtomsProof
open GorbowPRProgram SixSol20261113 List.Vector HistoryRuleSuffix.NativeProof
open GorbowSyntaxValidation
abbrev inputs (state token raw : Nat) : List.Vector Nat 3 := state ::ᵥ token ::ᵥ raw ::ᵥ nil
/-- Concrete list-code arithmetic; no closed replacement assumption here. -/
theorem singletonAt (state token raw : Nat) :
 evaluate singletonCode (inputs state token raw) = Encodable.encode [token] := by
 simp only [singletonCode,twoEval,projectionEval,constantEval,inputs]
 rw [HistoryCodec.NativeProof.nativeConsAllVectors]
 rfl
theorem variableAt (state token raw : Nat) :
 evaluate variableCode (inputs state token raw) = Encodable.encode [0,token] := by
 rw [variableCode,twoEval,constantEval,singletonAt,HistoryCodec.NativeProof.nativeConsAllVectors]
 rfl
theorem stackAt (tasks : List Task) (token raw : Nat) :
 evaluate stackCode (inputs (Encodable.encode (some tasks : State)) token raw) = Encodable.encode tasks := by
 simp only [stackCode,oneEval,projectionEval,inputs]
 rw [HistoryCodec.NativeProof.evaluatePredecessor]
 rfl
theorem taskAt (task : Task) (rest : List Task) (token raw : Nat) :
 evaluate taskCode (inputs (Encodable.encode (some (task::rest) : State)) token raw) = Encodable.encode task := by
 rw [taskCode,oneEval,stackAt,HistoryLookup.NativeProof.headCons]
theorem kindAt (k bound : Nat) (rest : List Task) (token raw : Nat) :
 evaluate kindCode (inputs (Encodable.encode (some ((k,bound)::rest) : State)) token raw) = k := by
 rw [kindCode,oneEval,taskAt,HistoryDecoder.NativeProof.evaluateDecoder]
 simp only [HistoryDispatcher.NativeProof.encodeProd,HistoryDispatcher.NativeProof.encodeNat,
  Nat.unpair_pair,HistoryDecoder.NativeProof.coordinate,ite_false,Bool.false_eq_true]
theorem boundAt (k bound : Nat) (rest : List Task) (token raw : Nat) :
 evaluate boundCode (inputs (Encodable.encode (some ((k,bound)::rest) : State)) token raw) = bound := by
 rw [boundCode,oneEval,taskAt,HistoryDecoder.NativeProof.evaluateDecoder]
 simp only [HistoryDispatcher.NativeProof.encodeProd,HistoryDispatcher.NativeProof.encodeNat,
  Nat.unpair_pair,HistoryDecoder.NativeProof.coordinate,ite_true]
theorem depthAt (k bound : Nat) (rest : List Task) (token raw : Nat) :
 evaluate depthCode (inputs (Encodable.encode (some ((k,bound)::rest) : State)) token raw) = bound-1 := by
 rw [depthCode,oneEval,boundAt,HistoryCodec.NativeProof.evaluatePredecessor]
 rfl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit.NativeAtomsProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit.NativeAtomsProof
