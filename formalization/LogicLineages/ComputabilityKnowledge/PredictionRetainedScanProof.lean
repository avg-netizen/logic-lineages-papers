module

public import LogicLineages.ComputabilityKnowledge.PredictionRetainedScanTargets
public import LogicLineages.ComputabilityKnowledge.PredictionCanonicalListProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionRetainedScanProof
open PredictionCanonicalList PredictionRetainedScan PredictionRetainedScanTargets

theorem earlierRetainedScanCalibration : EarlierRetainedScanCalibration := by
  intro i
  constructor
  · intro h
    exact ⟨h.1, fun j hj _ => h.2 j hj⟩
  · rintro ⟨htotal, hretained⟩
    refine ⟨htotal, ?_⟩
    intro j hji hequal
    have hjtotal : TotalNat (codeAt j) := by
      intro n
      obtain ⟨v, hv⟩ := htotal n
      exact ⟨v, by rw [hequal n]; exact hv⟩
    obtain ⟨k, ⟨hk, hkj⟩, _⟩ := PredictionCanonicalListProof.uniqueLeastRepresentative (codeAt j) hjtotal
    have hkle : k ≤ j := by
      by_contra h
      have hjk : j < k := by omega
      exact hk.2 j hjk (fun n => (hkj n).symm)
    have hki : SameFunction (codeAt k) (codeAt i) := fun n => (hkj n).trans (hequal n)
    exact hretained k (by omega) hk hki

end LogicLineages.ComputabilityKnowledge.PredictionRetainedScanProof
