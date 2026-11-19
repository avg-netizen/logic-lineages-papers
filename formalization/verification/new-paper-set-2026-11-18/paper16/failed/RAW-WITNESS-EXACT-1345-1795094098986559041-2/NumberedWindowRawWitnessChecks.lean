import LogicLineages.PersistentMarking.NumberedWindowRawWitnessComplete
import LogicLineages.PersistentMarking.NumberedWindowRawWitnessContextSound
import LogicLineages.PersistentMarking.NumberedWindowTypingBitsChecks

namespace LogicLineages.PersistentMarking.NumberedWindowRawWitnessChecks
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules
open NumberedWindowRawWitnessBits NumberedWindowRawWitnessTargets

theorem exact_PrecedenceBit : ExactPrecedenceBit :=
  NumberedWindowRawWitnessLaws.precedes

theorem exact_EquivalentHeadBit : ExactEquivalentHeadBit :=
  NumberedWindowRawWitnessLaws.equivalent

theorem exact_SuppliedRawWitnessSound : SuppliedRawWitnessSound :=
  NumberedWindowRawWitnessContextSound.supplied

theorem exact_CertifiedRawStep : ExactCertifiedRawStep := by
  intro S K Q R
  exact ⟨fun ⟨w,h⟩ => NumberedWindowRawWitnessContextSound.term S K w Q R h,
    NumberedWindowRawWitnessComplete.term⟩

theorem exact_CertifiedRawArgsStep : ExactCertifiedRawArgsStep := by
  intro S K qs rs
  exact ⟨fun ⟨i,w,h⟩ => NumberedWindowRawWitnessContextSound.args S K i w qs rs h,
    NumberedWindowRawWitnessComplete.args⟩

theorem exact_CertifiedFiniteWindowStep : ExactCertifiedFiniteWindowStep := by
  intro S K Γ τ Q R
  have hwQ := NumberedWindowTypingBitsChecks.exact_FiniteWindowBit S K Γ τ Q
  have hwR := NumberedWindowTypingBitsChecks.exact_FiniteWindowBit S K Γ τ R
  constructor
  · rintro ⟨w,h⟩
    simp only [finiteWindowWitnessBit,Bool.and_eq_true,hwQ,hwR] at h
    exact ⟨NumberedWindowRawWitnessContextSound.term S K w Q R h.1.1,h.1.2,h.2⟩
  · intro h
    obtain ⟨w,hw⟩ := NumberedWindowRawWitnessComplete.term h.1
    refine ⟨w,?_⟩
    simp only [finiteWindowWitnessBit,Bool.and_eq_true,hwQ,hwR]
    exact ⟨⟨hw,h.2.1⟩,h.2.2⟩

#print axioms exact_PrecedenceBit
#print axioms exact_EquivalentHeadBit
#print axioms exact_SuppliedRawWitnessSound
#print axioms exact_CertifiedRawStep
#print axioms exact_CertifiedRawArgsStep
#print axioms exact_CertifiedFiniteWindowStep

end LogicLineages.PersistentMarking.NumberedWindowRawWitnessChecks
