module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticWitnessListCodeProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticRawRootCode

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticReplacementCodeProof
open NumberedWindowPrimitiveWitnessBits
open NumberedWindowArithmeticFields NumberedWindowArithmeticNodeProof
open NumberedWindowArithmeticRawRootCode NumberedWindowArithmeticWitnessListCodeProof

theorem flagSound (n : Nat) (b : Bool) (h : decodeFlag n = some b) : encodeFlag b = n := by
  unfold decodeFlag at h
  split at h
  · cases h; rfl
  · cases h; rfl
  · cases h

theorem flagRound (b : Bool) : decodeFlag (encodeFlag b) = some b := by
  cases b <;> rfl

private theorem assembleSound (tag : Nat) (xs : List Nat) (w : ReplacementWitness)
    (h : assembleReplacement tag xs = some w) : encodeReplacement w = encodeNode tag xs := by
  unfold assembleReplacement at h
  split at h
  · simp only [Option.bind_eq_bind,Option.bind_eq_some_iff,Option.pure_def,Option.some.injEq] at h
    obtain ⟨kept,hk,removed,hr,added,ha,rfl⟩ := h
    simp only [encodeReplacement,termsSound _ _ hk,termsSound _ _ hr,termsSound _ _ ha]
  · cases h

theorem partSound (n : Nat) (w : ReplacementWitness) (h : decodeReplacement n = some w) :
    encodeReplacement w = n := by
  change (decodeNode n).bind (fun p => assembleReplacement p.1 p.2) = some w at h
  obtain ⟨p,hn,hw⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨tag,xs⟩ := p
  exact (assembleSound tag xs w hw).trans (nodeRead hn)

theorem partRound (w : ReplacementWitness) : decodeReplacement (encodeReplacement w) = some w := by
  cases w with
  | mk ks rs as' =>
    simp [decodeReplacement,encodeReplacement,nodeRound,assembleReplacement,termsRound]

end LogicLineages.PersistentMarking.NumberedWindowArithmeticReplacementCodeProof
