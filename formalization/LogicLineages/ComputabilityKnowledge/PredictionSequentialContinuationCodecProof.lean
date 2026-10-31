module
public import LogicLineages.ComputabilityKnowledge.PredictionSequentialContinuationCodecTargets
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionSequentialContinuationCodec

theorem listRoundtrip : Targets.ListRoundtrip := by
  constructor
  · intro k
    induction k <;> simp_all [toList, fromList, push]
  · intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      cases x with
      | none => simp_all [fromList, push, toList]
      | some x =>
        cases x with
        | inl c => simp_all [fromList, push, toList]
        | inr x => cases x <;> simp_all [fromList, push, toList]

theorem roundtrip : Targets.Roundtrip := by
  intro k
  simp only [decode, code, Encodable.encodek, Option.getD_some]
  exact listRoundtrip.1 k

theorem foldCorrect : Targets.FoldCorrect := by
  intro α z step k
  induction k <;> simp_all [toList, fold]

def listEquiv : Cont ≃ List Frame where
  toFun := toList
  invFun := fromList
  left_inv := listRoundtrip.1
  right_inv := listRoundtrip.2

instance contPrimcodable : Primcodable Cont := Primcodable.ofEquiv (List Frame) listEquiv

theorem actualPrimcodable : Targets.ActualPrimcodable := ⟨contPrimcodable, rfl⟩

theorem foldPrimitiveRecursive : Targets.FoldPrimitiveRecursive := by
  intro i hi α inst z step hstep
  letI : Primcodable Cont := i
  have hl : Primrec toList := by
    apply Primrec.encode_iff.mp
    have he : Primrec (@Encodable.encode Cont i.toEncodable) := Primrec.encode
    change Primrec code
    exact he.of_eq (fun k => congrFun hi k)
  have hf : Primrec (fun k : Cont => (toList k).foldr step z) :=
    Primrec.list_foldr hl (Primrec.const z) (hstep.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  exact hf.of_eq (fun k => foldCorrect α z step k)
end LogicLineages.ComputabilityKnowledge.PredictionSequentialContinuationCodec
