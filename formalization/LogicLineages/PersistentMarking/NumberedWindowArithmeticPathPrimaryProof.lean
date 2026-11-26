import LogicLineages.PersistentMarking.NumberedWindowArithmeticPathDecodeProof

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticPathPrimaryProof
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticPathCode
open NumberedWindowArithmeticRawWitnessCode NumberedWindowArithmeticRawHopCodeProof
open NumberedWindowArithmeticPathCheckBits NumberedWindowArithmeticPathCheckTargets
open NumberedWindowArithmeticPathDecodeProof
open NumberedWindowTypingBits NumberedWindowTypingBitsChecks
open NumberedWindowPrimaryClassList NumberedWindowPrimaryClassListChecks
open NumberedWindowRawWitnessBits NumberedWindowPathWitnessBits

theorem primary : ExactPrimaryOnCodes := by
  intro S K Γ τ src dst hk
  constructor
  · intro h
    cases hQ : decodeTerm src with
    | none => simp [primaryCodeBit,hQ] at h
    | some Q =>
      cases hR : decodeTerm dst with
      | none => simp [primaryCodeBit,hQ,hR] at h
      | some R =>
        simp only [primaryCodeBit,hQ,hR,Bool.and_eq_true] at h
        have wQ := (exact_FiniteWindowBit S K Γ τ Q).mp h.1.1
        have wR := (exact_FiniteWindowBit S K Γ τ R).mp h.1.2
        exact ⟨Q,R,termRead hQ,termRead hR,wQ,wR,
          (exact_FinitePrimaryDecision S K Γ τ Q R hk wQ).mp h.2⟩
  · rintro ⟨Q,R,hQ,hR,wQ,wR,h⟩
    simp only [primaryCodeBit,termAt hQ,termAt hR,
      Bool.and_eq_true,exact_FiniteWindowBit S K Γ τ Q,exact_FiniteWindowBit S K Γ τ R]
    exact ⟨⟨wQ,wR⟩,(exact_FinitePrimaryDecision S K Γ τ Q R hk wQ).mpr h⟩

theorem malformed : CodedChecksRejectMalformed := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro S K Γ τ src c dst h
    exact betweenMalformed decodeWitness
      (fun Q w R => finiteWindowWitnessBit S K Γ τ w Q R) src c dst h
  · intro S K Γ τ src c dst h
    exact betweenMalformed decodeRawPath (rawPathBit S K Γ τ) src c dst h
  · intro S K Γ τ src c dst h
    simp [classEdgeCodeBit,h]
  · intro S K Γ τ src c dst h
    simp [positiveClassPathCodeBit,h]
  · intro S K Γ τ src dst h
    rcases h with h | h
    · cases hR : decodeTerm dst <;> simp [primaryCodeBit,h,hR]
    · cases hQ : decodeTerm src <;> simp [primaryCodeBit,hQ,h]

end LogicLineages.PersistentMarking.NumberedWindowArithmeticPathPrimaryProof
