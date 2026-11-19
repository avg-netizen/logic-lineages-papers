import LogicLineages.PersistentMarking.ProtectedSpineCompletenessThinChecks
import LogicLineages.PersistentMarking.ProtectedSpineSoundInterpreterProof

namespace LogicLineages.PersistentMarking.ProtectedSpineAdequacyThinChecks
open ProtectedSpineAdequacyTargets

theorem exact_ExactObservation : ExactObservation := by
  intro S F Γ q t σ hw hu ho hq ht
  have hc := ProtectedSpineCompletenessThinChecks.exact_CompleteObservation S F Γ q t σ hw hu ho hq ht
  have hs := ProtectedSpineSoundInterpreterProof.exact_SoundObservation S F Γ q t σ hw hu ho hq ht
  exact ⟨⟨hs.1,hc.1⟩,⟨hs.2,hc.2⟩⟩

#print axioms exact_ExactObservation
end LogicLineages.PersistentMarking.ProtectedSpineAdequacyThinChecks
