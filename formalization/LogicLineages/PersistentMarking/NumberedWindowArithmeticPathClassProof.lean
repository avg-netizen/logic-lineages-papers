import LogicLineages.PersistentMarking.NumberedWindowArithmeticPathWindowProof

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticPathClassProof
open NumberedWindowClassPathWitnessBits NumberedWindowPathWitnessChecks
open NumberedWindowArithmeticPathCode NumberedWindowArithmeticPathCodeChecks
open NumberedWindowArithmeticPathCheckBits NumberedWindowArithmeticPathCheckTargets

theorem edge : ExactClassEdgeOnCodes := by
  intro S K Γ τ src dst hk
  have hExact := exact_CertifiedNumericClassEdge S K Γ τ src dst hk
  constructor
  · rintro ⟨c,h⟩
    cases hw : decodeClassEdge c with
    | none => simp [classEdgeCodeBit,hw] at h
    | some w =>
      exact hExact.mp ⟨w,by simpa only [classEdgeCodeBit,hw] using h⟩
  · intro h
    obtain ⟨w,hw⟩ := hExact.mpr h
    exact ⟨encodeClassEdge w,by
      simpa only [classEdgeCodeBit,exact_ClassEdgeWitnessCodec.2.1 w] using hw⟩

theorem path : ExactPositiveClassPathOnCodes := by
  intro S K Γ τ src dst hk
  have hExact := exact_CertifiedPositiveNumericClassPath S K Γ τ src dst hk
  constructor
  · rintro ⟨c,h⟩
    cases hw : decodeClassPath c with
    | none => simp [positiveClassPathCodeBit,hw] at h
    | some w =>
      exact hExact.mp ⟨w,by simpa only [positiveClassPathCodeBit,hw] using h⟩
  · intro h
    obtain ⟨w,hw⟩ := hExact.mpr h
    exact ⟨encodeClassPath w,by
      simpa only [positiveClassPathCodeBit,exact_ClassPathListCodec.2.1 w] using hw⟩

end LogicLineages.PersistentMarking.NumberedWindowArithmeticPathClassProof
