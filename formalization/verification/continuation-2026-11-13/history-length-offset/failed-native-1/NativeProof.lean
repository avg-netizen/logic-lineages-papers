module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthOffset.Targets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthOffset.NativeProof
open GorbowPRProgram List.Vector HistoryRuleSuffix.NativeProof

theorem dropZeroIff {α : Type} [Encodable α] (xs : List α) (i : Nat) :
    Encodable.encode (xs.drop i)=0 ↔ xs.length≤i := by
  induction i generalizing xs with
  | zero => cases xs with
    | nil => simp
    | cons a xs =>
        change (Nat.pair (Encodable.encode a) (Encodable.encode xs)).succ=0 ↔ xs.length+1≤0
        omega
  | succ i ih => cases xs with
    | nil => simp
    | cons a xs => simpa only [List.drop_succ_cons,List.length_cons,Nat.succ_le_succ_iff] using ih xs

theorem stepEval (i previous code : Nat) :
    evaluate countStep (i ::ᵥ previous ::ᵥ code ::ᵥ nil) =
      if evaluate HistoryLookup.drop (i ::ᵥ code ::ᵥ nil)=0 then previous else previous+1 := by
  simp only [countStep,chooseEval,suffixAt,twoEval,oneEval,projectionEval,get3_0,get3_1,get3_2]
  rfl

theorem countEval {α : Type} [Encodable α] (bound : Nat) (xs : List α) :
    evaluate count (bound ::ᵥ Encodable.encode xs ::ᵥ nil)=min bound xs.length := by
  induction bound with
  | zero => rfl
  | succ b ih =>
      change evaluate countStep (b ::ᵥ evaluate count (b ::ᵥ Encodable.encode xs ::ᵥ nil) ::ᵥ Encodable.encode xs ::ᵥ nil) = _
      rw [stepEval,ih,HistoryLookup.NativeProof.evaluateDrop,dropZeroIff]
      split <;> omega

theorem lengthBound {α : Type} [Encodable α] (xs : List α) : xs.length≤Encodable.encode xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      rw [List.length_cons,HistoryLookup.NativeProof.encodeCons]
      have h := Nat.right_le_pair (Encodable.encode a) (Encodable.encode xs)
      omega

theorem lengthList {α : Type} [Encodable α] (xs : List α) :
    evaluate lengthProgram (Encodable.encode xs ::ᵥ nil)=xs.length := by
  change evaluate count (Encodable.encode xs ::ᵥ Encodable.encode xs ::ᵥ nil)=_
  rw [countEval,Nat.min_eq_right (lengthBound xs)]

theorem nativeLength : Targets.NativeLength := by
  constructor
  · intro v
    obtain ⟨xs,hencode,hdecode⟩ := LiteralCheckerAuxiliaries.CodecProof.certificateCodecTotal (v.get 0)
    have hv : v = v.get 0 ::ᵥ nil := by
      rw [List.Vector.get_zero]
      simpa only [List.Vector.eq_nil] using (List.Vector.cons_head_tail v).symm
    rw [hv]
    change evaluate lengthProgram (v.get 0 ::ᵥ nil) = ((GorbowNumericCertificate.decodeCertificate (v.get 0)).getD []).length
    rw [hdecode]
    simpa only [hencode,Option.getD_some] using lengthList xs
  · exact lengthList
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthOffset.NativeProof
