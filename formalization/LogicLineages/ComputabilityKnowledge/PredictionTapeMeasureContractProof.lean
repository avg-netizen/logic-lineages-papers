module
public import LogicLineages.ComputabilityKnowledge.PredictionTapeMeasureContractTargets
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeMeasureContractProof
open PredictionGame PredictionTapeRuntimeClass PredictionTapeMeasureContract PredictionTapeMeasureContractTargets

theorem thresholdAntitone : ThresholdAntitone := by
  intro p b c hbc hc e he htime
  apply hc e he
  obtain ⟨N, hN⟩ := htime
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨t, ht, hb⟩ := hN n hn
  exact ⟨t, ht, lt_of_lt_of_le hb (hbc n)⟩

theorem infiniteCharacterization : InfiniteCharacterization := by
  classical
  intro levels p
  unfold height
  split_ifs with h
  · constructor
    · intro he
      exact False.elim (WithTop.coe_ne_top he)
    · intro hall
      obtain ⟨m, hm, hn⟩ := h
      exact False.elim (hn (hall m hm))
  · simp only [true_iff]
    intro m hm
    by_contra hn
    exact h ⟨m, hm, hn⟩

theorem zeroCharacterization : ZeroCharacterization := by
  classical
  intro levels p
  constructor
  · intro hz
    by_cases h : ∃ m, 1 ≤ m ∧ ¬ Threshold p (levels m)
    · have hh : Nat.find h - 1 = 0 := by
        have he : ((Nat.find h - 1 : Nat) : WithTop Nat) = (0 : WithTop Nat) := by
          simpa only [height, dif_pos h] using hz
        exact WithTop.coe_injective he
      have hm := Nat.find_spec h
      have hi : Nat.find h = 1 := by omega
      simpa [hi] using hm.2
    · have he : (⊤ : WithTop Nat) = 0 := by simpa only [height, dif_neg h] using hz
      exact False.elim (WithTop.top_ne_coe he)
  · intro hn
    have h : ∃ m, 1 ≤ m ∧ ¬ Threshold p (levels m) := ⟨1, le_rfl, hn⟩
    have hle : Nat.find h ≤ 1 := Nat.find_min' h ⟨le_rfl, hn⟩
    have hge := (Nat.find_spec h).1
    have hi : Nat.find h = 1 := by omega
    simp only [height, dif_pos h, hi, Nat.sub_self]
    rfl

theorem finiteCharacterization : FiniteCharacterization := by
  classical
  intro levels hmono p h hh
  constructor
  · intro he
    have hex : ∃ m, 1 ≤ m ∧ ¬ Threshold p (levels m) := by
      by_contra hn
      have ht : (⊤ : WithTop Nat) = (h : WithTop Nat) := by simpa only [height, dif_neg hn] using he
      exact WithTop.top_ne_coe ht
    have hfind : Nat.find hex - 1 = h := by
      have hf : ((Nat.find hex - 1 : Nat) : WithTop Nat) = (h : WithTop Nat) := by
        simpa only [height, dif_pos hex] using he
      exact WithTop.coe_injective hf
    have hspec := Nat.find_spec hex
    have hi : Nat.find hex = h + 1 := by omega
    constructor
    · by_contra hn
      exact Nat.find_min hex (by omega : h < Nat.find hex) ⟨hh, hn⟩
    · simpa [hi] using hspec.2
  · rintro ⟨ht, hnot⟩
    have hex : ∃ m, 1 ≤ m ∧ ¬ Threshold p (levels m) := ⟨h + 1, by omega, hnot⟩
    have hle : Nat.find hex ≤ h + 1 := Nat.find_min' hex ⟨by omega, hnot⟩
    have hs := Nat.find_spec hex
    have hgt : h < Nat.find hex := by
      by_contra hn
      exact hs.2 (thresholdAntitone p (levels (Nat.find hex)) (levels h)
        (fun n => hmono n (by omega)) ht)
    have hi : Nat.find hex = h + 1 := by omega
    simp only [height, dif_pos hex, hi, Nat.add_sub_cancel]

end LogicLineages.ComputabilityKnowledge.PredictionTapeMeasureContractProof
