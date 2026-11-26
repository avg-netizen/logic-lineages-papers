module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit.ClosedShiftProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit.NativeAtomsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit.NativeProof
open GorbowPRProgram SixSol20261113 List.Vector HistoryRuleSuffix.NativeProof
open GorbowSyntaxValidation NativeAtomsProof
/-- Truncated difference orientation is the original depth-token. -/
theorem indexAt (k bound : Nat) (rest : List Task) (token raw : Nat) :
 evaluate indexCode (inputs (Encodable.encode (some ((k,bound)::rest) : State)) token raw) =
 if token < bound-1 then Encodable.encode [0,token] else if token = bound-1 then raw else 0 := by
 simp only [indexCode,chooseEval,twoEval,projectionEval,depthAt,HistoryCodec.NativeProof.evaluateDifference,
  HistoryRuleSuffix.NativeProof.equalEval,constantEval,variableAt,inputs,get3_1,get3_2]
 by_cases hl : token < bound-1
 · have hd : bound-1-token ≠ 0 := by omega
   simp [hl,hd]
 · have hd : bound-1-token = 0 := by omega
   by_cases he : token = bound-1 <;> simp [hl,hd,he]
theorem nonIndexAt (k bound : Nat) (rest : List Task) (token raw : Nat) :
 evaluate nonIndexCode (inputs (Encodable.encode (some ((k,bound)::rest) : State)) token raw) =
 if k=0 ∧ token=0 then 0 else Encodable.encode [token] := by
 simp only [nonIndexCode,chooseEval,twoEval,projectionEval,kindAt,constantEval,
  HistoryRuleSuffix.NativeProof.equalEval,singletonAt,inputs,get3_1]
 by_cases hk : k=0 <;> by_cases ht : token=0 <;> simp [hk,ht]
theorem activeAt (k bound : Nat) (rest : List Task) (token : Nat) (raw : List Nat)
 (hv : GorbowSyntaxValidation.validTerm 0 raw = true) :
 evaluate activeCode (inputs (Encodable.encode (some ((k,bound)::rest) : State)) token (Encodable.encode raw)) =
 Encodable.encode (GorbowSubstitutionCode.emit 1 0 [raw] (some ((k,bound)::rest)) token) := by
 rw [activeCode,chooseEval,twoEval,kindAt,constantEval,HistoryRuleSuffix.NativeProof.equalEval]
 by_cases hk : k=2
 · rw [if_pos hk]
   simp only [show (1:Nat) ≠ 0 from by decide,if_false]
   rw [indexAt]
   simp only [GorbowSubstitutionCode.emit,hk,ite_true,ClosedShiftProof.liftedSingleton (bound-1) token raw hv]
   split <;> rename_i ht
   · rfl
   · split <;> rfl
 · rw [if_neg hk]
   simp only [ite_true]
   rw [nonIndexAt]
   simp only [GorbowSubstitutionCode.emit,hk,ite_false]
   split <;> rfl
/-- Exact original emitter on the whole State domain, not only successful scans. -/
theorem exactOriginalEmit : Targets.ExactOriginalEmit := by
 intro s token raw hv
 cases s with
 | none =>
   change evaluate emitCode (inputs 0 token (Encodable.encode raw)) = _
   rw [emitCode,chooseEval]
   simp only [projectionEval,inputs,ite_true]
   exact singletonAt 0 token (Encodable.encode raw)
 | some tasks =>
   cases tasks with
   | nil =>
     change evaluate emitCode (inputs 1 token (Encodable.encode raw)) = _
     rw [emitCode,chooseEval]
     simp only [projectionEval,inputs,show (1:Nat) ≠ 0 from by decide,if_false]
     rw [chooseEval]
     have hz : evaluate stackCode (inputs 1 token (Encodable.encode raw)) = 0 :=
      stackAt [] token (Encodable.encode raw)
     rw [hz,if_pos rfl]
     exact singletonAt 1 token (Encodable.encode raw)
   | cons task rest =>
     rcases task with ⟨k,bound⟩
     change evaluate emitCode (inputs (Encodable.encode (some ((k,bound)::rest) : State)) token (Encodable.encode raw)) = _
     rw [emitCode,chooseEval]
     have hs : evaluate (.projection 0 : Program 3)
       (inputs (Encodable.encode (some ((k,bound)::rest) : State)) token (Encodable.encode raw)) ≠ 0 := Nat.succ_ne_zero _
     rw [if_neg hs,chooseEval,stackAt]
     have hn : Encodable.encode ((k,bound)::rest) ≠ 0 := by
      rw [HistoryLookup.NativeProof.encodeCons]
      exact Nat.succ_ne_zero _
     rw [if_neg hn]
     exact activeAt k bound rest token raw hv
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit.NativeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionEmit.NativeProof
