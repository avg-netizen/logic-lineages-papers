module
public import LogicLineages.ComputabilityKnowledge.PredictionTapeRuntimeTargets
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeRuntime
open PredictionFiniteAlphabet

private theorem not_success_zero (code : Nat) (xs : List Bool) : ¬ Successful code xs 0 := by
  rintro ⟨d, hd⟩
  simp [simulate, bounded] at hd

private theorem success_mono {code : Nat} {xs : List Bool} {a b : Nat}
    (h : Successful code xs a) (hab : a ≤ b) : Successful code xs b := by
  obtain ⟨d, hd⟩ := h
  obtain ⟨n, hn, hr, hnone⟩ := (PredictionFiniteAlphabetProof.exactBoundedSimulation
    (decodeTable code) a (initial (decodeTable code) xs) d).mp hd
  exact ⟨d, (PredictionFiniteAlphabetProof.exactBoundedSimulation
    (decodeTable code) b (initial (decodeTable code) xs) d).mpr ⟨n, by omega, hr, hnone⟩⟩

theorem runtimeThreshold : Targets.RuntimeThreshold := by
  intro code xs t
  constructor
  · rintro ⟨hs, hmin⟩ fuel
    constructor
    · intro hf
      by_contra hle
      exact hmin fuel (by omega) hf
    · intro hle
      exact success_mono hs hle
  · intro h
    refine ⟨(h t).mpr le_rfl, ?_⟩
    intro fuel hf hs
    have := (h fuel).mp hs
    omega

private theorem runtime_bounded {code : Nat} {xs : List Bool} {fuel : Nat}
    (h : Successful code xs fuel) : ∃ t, Runtime code xs t ∧ t ≤ fuel := by
  classical
  have hex : ∃ t, Successful code xs t := ⟨fuel,h⟩
  exact ⟨Nat.find hex, ⟨Nat.find_spec hex, fun u hu => Nat.find_min hex hu⟩, Nat.find_min' hex h⟩

private theorem not_all_zero (code n : Nat) :
    ¬ ∀ xs : List Bool, xs.length=n → Successful code xs 0 := by
  intro h
  exact not_success_zero code (List.replicate n false) (h _ (by simp))

theorem worstTimeThreshold : Targets.WorstTimeThreshold := by
  classical
  intro code n t
  constructor
  · rintro ⟨hall, xs, hxs, hxt⟩ fuel
    constructor
    · intro hf
      exact ((runtimeThreshold code xs t).mp hxt fuel).mp (hf xs hxs)
    · intro htf ys hys
      obtain ⟨s, hs, hst⟩ := hall ys hys
      exact ((runtimeThreshold code ys s).mp hs fuel).mpr (hst.trans htf)
  · intro h
    have hallt := (h t).mpr le_rfl
    have hall : ∀ xs : List Bool, xs.length=n → ∃ s, Runtime code xs s ∧ s ≤ t :=
      fun xs hx => runtime_bounded (hallt xs hx)
    have htpos : 0<t := by
      by_contra ht
      have ht0 : t=0 := by omega
      exact not_all_zero code n (ht0 ▸ hallt)
    have hnot : ¬ ∀ xs : List Bool, xs.length=n → Successful code xs (t-1) := by
      intro hall'
      have := (h (t-1)).mp hall'
      omega
    push_neg at hnot
    obtain ⟨xs, hxs, hfail⟩ := hnot
    obtain ⟨s, hs, hst⟩ := hall xs hxs
    have hts : t ≤ s := by
      by_contra hh
      exact hfail (((runtimeThreshold code xs s).mp hs (t-1)).mpr (by omega))
    have heq : s=t := by omega
    exact ⟨hall, xs, hxs, heq ▸ hs⟩

private theorem histories_mem (n : Nat) (xs : List Bool) : xs ∈ histories n ↔ xs.length=n := by
  induction n generalizing xs with
  | zero => simp [histories]
  | succ n ih =>
    cases xs with
    | nil => simp [histories]
    | cons b xs => cases b <;> simp [histories, ih]

private theorem finite_uniform (code : Nat) (ls : List (List Bool))
    (h : ∀ xs ∈ ls, ∃ fuel, Successful code xs fuel) :
    ∃ fuel, ∀ xs ∈ ls, Successful code xs fuel := by
  induction ls with
  | nil => exact ⟨0, by simp⟩
  | cons xs ls ih =>
    obtain ⟨a, ha⟩ := h xs (by simp)
    obtain ⟨b, hb⟩ := ih (fun ys hy => h ys (by simp [hy]))
    refine ⟨max a b, ?_⟩
    intro ys hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact success_mono ha (Nat.le_max_left _ _)
    · exact success_mono (hb ys hy) (Nat.le_max_right _ _)

private theorem worst_from_uniform {code n : Nat}
    (h : ∃ fuel, ∀ xs : List Bool, xs.length=n → Successful code xs fuel) :
    ∃ t, WorstTime code n t := by
  classical
  refine ⟨Nat.find h, (worstTimeThreshold code n (Nat.find h)).mpr ?_⟩
  intro fuel
  constructor
  · exact fun hf => Nat.find_min' h hf
  · intro hle xs hx
    exact success_mono (Nat.find_spec h xs hx) hle

theorem worstTimeDomain : Targets.WorstTimeDomain := by
  intro code n
  constructor
  · rintro ⟨t, hall, hat⟩ xs hx
    obtain ⟨s, hs, hst⟩ := hall xs hx
    exact ⟨s, hs.1⟩
  · intro h
    obtain ⟨fuel, hf⟩ := finite_uniform code (histories n)
      (fun xs hx => h xs ((histories_mem n xs).mp hx))
    exact worst_from_uniform ⟨fuel, fun xs hx => hf xs ((histories_mem n xs).mpr hx)⟩

theorem strictBudgetCalibration : Targets.StrictBudgetCalibration := by
  intro code n b
  constructor
  · rintro ⟨t, ht, htb⟩ xs hx
    exact ((worstTimeThreshold code n t).mp ht (b-1)).mpr (by omega) xs hx
  · intro h
    have hb : 0<b := by
      by_contra hh
      have heq : b=0 := by omega
      subst b
      exact not_all_zero code n h
    obtain ⟨t, ht⟩ := worst_from_uniform ⟨b-1, h⟩
    have hle := ((worstTimeThreshold code n t).mp ht (b-1)).mp h
    exact ⟨t, ht, by omega⟩

theorem totalBinaryWorstExists : Targets.TotalBinaryWorstExists := by
  intro code h n
  apply (worstTimeDomain code n).mpr
  intro xs hx
  obtain ⟨b, hb⟩ := h xs
  obtain ⟨budget, hm⟩ := (PredictionTapeObservationProof.exactBinarySemantics code xs b).mp hb
  unfold PredictionTapeObservation.boundedMove at hm
  obtain ⟨v, hv, hr⟩ := Option.bind_eq_some_iff.mp hm
  unfold PredictionTapeObservation.observe at hv
  obtain ⟨d, hd, he⟩ := Option.map_eq_some_iff.mp hv
  exact ⟨budget-1, d, hd⟩

theorem exactEvaderRuntime : Targets.ExactEvaderRuntime := by
  intro k xs
  apply (runtimeThreshold (evaderCode k) xs (min k xs.length+2)).mpr
  intro fuel
  exact PredictionAlphabetEmbeddingProof.exactEvaderRuntime k xs fuel

theorem exactEvaderWorstTime : Targets.ExactEvaderWorstTime := by
  intro k n
  constructor
  · intro xs hx
    refine ⟨min k n+2, ?_, le_rfl⟩
    simpa [hx] using exactEvaderRuntime k xs
  · refine ⟨List.replicate n false, by simp, ?_⟩
    simpa using exactEvaderRuntime k (List.replicate n false)

theorem eventualEvaderStrictBound : Targets.EventualEvaderStrictBound := by
  intro k
  refine ⟨k+2, ?_⟩
  intro n hn
  refine ⟨min k n+2, exactEvaderWorstTime k n, ?_⟩
  have := Nat.min_le_left k n
  omega
end LogicLineages.ComputabilityKnowledge.PredictionTapeRuntime
