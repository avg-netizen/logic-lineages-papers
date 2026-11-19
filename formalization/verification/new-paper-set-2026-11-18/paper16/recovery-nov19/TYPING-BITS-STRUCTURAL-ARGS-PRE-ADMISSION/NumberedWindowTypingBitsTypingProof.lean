import LogicLineages.PersistentMarking.NumberedWindowTypingBitsCasesProof

namespace LogicLineages.PersistentMarking.NumberedWindowTypingBitsTypingProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowTypingBits
open NumberedWindowTypingBitsTargets NumberedWindowTypingBitsCasesProof
open NumberedWindowTypingBitsArgsProof
open NumberedWindowApplicationDomainProof (annotation)

private theorem terms (Q : NTerm) : TermGoal Q := by
  induction Q using NTerm.rec (motive_2 := ArgsGoal) with
  | free σ x => exact freeCase σ x
  | bound σ i => exact boundCase σ i
  | lam σ Q iq => exact lamCase σ Q iq
  | bottom σ => exact bottomCase σ
  | ordinary f bs ib => exact ordinaryCase f bs ib
  | numbered f τ k bs es ib ie => exact numberedCase f τ k bs es ib ie
  | auxApp σ τ Q A iq ia => exact auxCase σ τ Q A iq ia
  | nil => exact nilCase
  | cons Q qs iq ia => exact consCase Q qs iq ia

private theorem args (qs : NArgs) : ArgsGoal qs := by
  induction qs with
  | nil => exact nilCase
  | cons Q qs ia => exact consCase Q qs (terms Q) ia

theorem typed : ExactTypedBit := by
  intro C τ Q
  simp only [typedBit,Bool.and_eq_true,decide_eq_true_eq,terms]
  constructor
  · rintro ⟨e,h⟩
    exact e ▸ h
  · intro h
    have e := annotation h
    exact ⟨e,e.symm ▸ h⟩

theorem base : ExactBaseBit := by
  intro C types qs
  simp only [baseBit,Bool.and_eq_true,decide_eq_true_eq,args]
  constructor
  · rintro ⟨e,h⟩
    exact e ▸ h
  · intro h
    have e := (baseShape h).1
    exact ⟨e,e.symm ▸ h⟩

theorem extras : ExactExtrasBit := by
  intro C qs
  rw [extrasBit,args qs C]
  exact ⟨fun h => (baseShape h).2,extrasBase⟩

end LogicLineages.PersistentMarking.NumberedWindowTypingBitsTypingProof
