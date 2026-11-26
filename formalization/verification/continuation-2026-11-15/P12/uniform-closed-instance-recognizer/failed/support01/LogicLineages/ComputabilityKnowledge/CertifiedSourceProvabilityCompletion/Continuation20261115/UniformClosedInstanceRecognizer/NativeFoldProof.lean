module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedInstanceRecognizer.Targets
public import Mathlib.Tactic.FinCases
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedInstanceRecognizer.NativeFoldProof
open GorbowPRProgram SixSol20261113 List.Vector HistoryRuleSuffix.NativeProof
open LiteralRawMP.NativeProof (pairEval)
/-- Calibration of the actual length-driven fold, on all old states and raw
token lists. Replacement closure is used here, not assumed on rejected inputs. -/
theorem foldAt (s : GorbowSubstitutionCode.OutputState) (tokens raw : List Nat)
 (hr : GorbowSyntaxValidation.validTerm 0 raw = true) :
 evaluate UniformClosedSubstitutionRawFold.foldCode
  (Encodable.encode tokens ::ᵥ Encodable.encode s ::ᵥ Encodable.encode raw ::ᵥ nil) =
 Encodable.encode (tokens.foldl (GorbowSubstitutionCode.subStep 1 0 [raw]) s) := by
 let v := Encodable.encode tokens ::ᵥ Encodable.encode s ::ᵥ Encodable.encode raw ::ᵥ nil
 have hp : evaluate UniformClosedSubstitutionRawFold.finalPacked v =
  Nat.pair 0 (Encodable.encode (tokens.foldl (GorbowSubstitutionCode.subStep 1 0 [raw]) s)) := by
  change evaluate UniformClosedSubstitutionFold.iterator _ = _
  convert UniformClosedSubstitutionFold.NativeProof.exactOriginalFold s tokens raw hr using 1
  ext i
  fin_cases i <;> simp only [v,List.Vector.get_ofFn,get3_0,get3_1,get3_2,oneEval,projectionEval,
   UniformClosedSubstitutionRawFold.initial,twoEval,HistoryLengthOffset.NativeProof.lengthList,pairEval]
 change evaluate (HistoryRuleSuffix.applyOne (HistoryDecoder.decoder true)
  UniformClosedSubstitutionRawFold.finalPacked) v = _
 rw [oneEval,hp,HistoryDecoder.NativeProof.evaluateDecoder]
 simp only [HistoryDecoder.NativeProof.coordinate,ite_true,Nat.unpair_pair]
/-- Literal original singleton formula task/state encoding; not a History codec. -/
theorem initialAt (a b : Nat) : evaluate initialState (a ::ᵥ b ::ᵥ nil) =
 Encodable.encode ((some [(1,1)],[]) : GorbowSubstitutionCode.OutputState) := by
 simp only [initialState,initialTasks,initialTask,twoEval,oneEval,constantEval,pairEval,
  HistoryCodec.NativeProof.nativeConsAllVectors]
 rfl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedInstanceRecognizer.NativeFoldProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedInstanceRecognizer.NativeFoldProof
