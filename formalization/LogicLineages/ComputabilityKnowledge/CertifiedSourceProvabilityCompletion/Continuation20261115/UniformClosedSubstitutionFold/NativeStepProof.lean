module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionFold.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralSyntaxStep.StatementChecks
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionFold.NativeStepProof
open GorbowPRProgram SixSol20261113 List.Vector HistoryRuleSuffix.NativeProof
open LiteralRawMP.NativeProof (pairEval)
theorem stateAt (s out token raw : Nat) :
 evaluate syntaxState (Nat.pair s out ::ᵥ token ::ᵥ raw ::ᵥ nil) = s := by
 simp only [syntaxState,oneEval,projectionEval,get3_0,HistoryDecoder.NativeProof.evaluateDecoder,
  Nat.unpair_pair,HistoryDecoder.NativeProof.coordinate,Bool.false_eq_true,ite_false]
theorem outputAt (s out token raw : Nat) :
 evaluate output (Nat.pair s out ::ᵥ token ::ᵥ raw ::ᵥ nil) = out := by
 simp only [output,oneEval,projectionEval,get3_0,HistoryDecoder.NativeProof.evaluateDecoder,
  Nat.unpair_pair,HistoryDecoder.NativeProof.coordinate,ite_true]
theorem emittedAt (s out token raw : Nat) :
 evaluate emitted (Nat.pair s out ::ᵥ token ::ᵥ raw ::ᵥ nil) =
 evaluate UniformClosedSubstitutionEmit.emitCode (s ::ᵥ token ::ᵥ raw ::ᵥ nil) := by
 unfold emitted
 change evaluate UniformClosedSubstitutionEmit.emitCode _ = _
 congr 1
 ext i
 cases i using Fin.cases with
 | zero => exact stateAt s out token raw
 | succ i => cases i using Fin.cases with
   | zero => rfl
   | succ i => cases i using Fin.cases with
     | zero => rfl
     | succ i => exact Fin.elim0 i
theorem subStepAt (s : GorbowSubstitutionCode.OutputState) (token : Nat) (raw : List Nat)
 (hr : GorbowSyntaxValidation.validTerm 0 raw = true) :
 evaluate subStepCode (Encodable.encode s ::ᵥ token ::ᵥ Encodable.encode raw ::ᵥ nil) =
 Encodable.encode (GorbowSubstitutionCode.subStep 1 0 [raw] s token) := by
 obtain ⟨state,out⟩ := s
 rw [HistoryDispatcher.NativeProof.encodeProd]
 simp only [subStepCode,twoEval,stateAt,outputAt,emittedAt,projectionEval,get3_1]
 rw [LiteralSyntaxStep.NativeProof.stepAt,UniformClosedSubstitutionEmit.StatementChecks.exactOriginalEmit state token raw hr,
  appendList,pairEval]
 rfl
theorem remainingAt (tokens state raw : Nat) :
 evaluate remaining (Nat.pair tokens state ::ᵥ raw ::ᵥ nil) = tokens := by
 simp only [remaining,oneEval,projectionEval,get2_0,HistoryDecoder.NativeProof.evaluateDecoder,
  Nat.unpair_pair,HistoryDecoder.NativeProof.coordinate,Bool.false_eq_true,ite_false]
theorem accumulatorAt (tokens state raw : Nat) :
 evaluate accumulator (Nat.pair tokens state ::ᵥ raw ::ᵥ nil) = state := by
 simp only [accumulator,oneEval,projectionEval,get2_0,HistoryDecoder.NativeProof.evaluateDecoder,
  Nat.unpair_pair,HistoryDecoder.NativeProof.coordinate,ite_true]
theorem advancedAt (tokens state raw : Nat) :
 evaluate advanced (Nat.pair tokens state ::ᵥ raw ::ᵥ nil) =
 evaluate subStepCode (state ::ᵥ evaluate HistoryLookup.head (tokens ::ᵥ nil) ::ᵥ raw ::ᵥ nil) := by
 unfold advanced
 change evaluate subStepCode _ = _
 congr 1
 ext i
 cases i using Fin.cases with
 | zero => exact accumulatorAt tokens state raw
 | succ i => cases i using Fin.cases with
   | zero => simp only [List.Vector.get_ofFn,oneEval,remainingAt,List.Vector.get_cons_succ,List.Vector.get_cons_zero]
   | succ i => cases i using Fin.cases with
     | zero => simp only [List.Vector.get_ofFn,List.Vector.get_cons_succ,List.Vector.get_cons_zero,projectionEval,get2_1]
     | succ i => exact Fin.elim0 i
theorem tickNil (state raw : Nat) :
 evaluate tick (Nat.pair 0 state ::ᵥ raw ::ᵥ nil) = Nat.pair 0 state := by
 simp only [tick,chooseEval,remainingAt,projectionEval,get2_0,if_pos rfl,ite_true]
theorem tickCons (token : Nat) (tokens : List Nat) (s : GorbowSubstitutionCode.OutputState) (raw : List Nat)
 (hr : GorbowSyntaxValidation.validTerm 0 raw = true) :
 evaluate tick (Nat.pair (Encodable.encode (token::tokens)) (Encodable.encode s) ::ᵥ Encodable.encode raw ::ᵥ nil) =
 Nat.pair (Encodable.encode tokens) (Encodable.encode (GorbowSubstitutionCode.subStep 1 0 [raw] s token)) := by
 simp only [tick,chooseEval,remainingAt,twoEval,oneEval,advancedAt,
  HistoryLookup.NativeProof.tailList,HistoryLookup.NativeProof.headCons,List.tail_cons,HistoryDispatcher.NativeProof.encodeNat]
 have hn : Encodable.encode (token::tokens) ≠ 0 := by
  rw [HistoryLookup.NativeProof.encodeCons]; exact Nat.succ_ne_zero _
 rw [if_neg hn,subStepAt s token raw hr,pairEval]
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionFold.NativeStepProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedSubstitutionFold.NativeStepProof
