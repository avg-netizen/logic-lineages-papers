module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPrimaryExchangeTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowPrimaryExchangeHeadProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowLiteralEquality
open NumberedWindowPrimaryExchange NumberedWindowPrimaryExchangeBits

theorem headPair (S : Spine.Signature) (K : List Ty) (f g : Head) :
    headPairBit S K f g = true ↔ AllowedHeadPair S K f g := by
  simp only [headPairBit,Bool.and_eq_true,NumberedWindowHeadEnumerationProof.bit,
    decide_eq_true_eq,AllowedHeadPair]
  constructor
  · rintro ⟨⟨hf,hg⟩,e⟩
    obtain ⟨i,hi⟩ := hg.1
    exact ⟨hf,hg,i,e.trans hi,hi⟩
  · rintro ⟨hf,hg,i,hf',hg'⟩
    exact ⟨⟨hf,hg⟩,hf'.trans hg'.symm⟩

theorem headSymm {S K f g} (h : AllowedHeadPair S K f g) : AllowedHeadPair S K g f := by
  obtain ⟨hf,hg,i,hrf,hrg⟩ := h
  exact ⟨hg,hf,i,hrg,hrf⟩

theorem permutation (bs cs : NArgs) : permutationBit bs cs = true ↔ bs.toList.Perm cs.toList := by
  simp only [permutationBit,decide_eq_true_eq]

theorem termIdentity (Q R : NTerm) : termEq Q R = true ↔ Q = R :=
  NumberedWindowTypingBitsChecks.exact_LiteralTermEquality Q R

theorem argsIdentity (qs rs : NArgs) : argsEq qs rs = true ↔ qs = rs :=
  NumberedWindowTypingBitsChecks.exact_LiteralArgsEquality qs rs

end LogicLineages.PersistentMarking.NumberedWindowPrimaryExchangeHeadProof
