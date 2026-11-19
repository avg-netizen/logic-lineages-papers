import LogicLineages.PersistentMarking.NumberedWindowArithmeticPairBoundsProof

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticPairDecodeProof
open NumberedWindowArithmeticPair NumberedWindowArithmeticPairTargets
open NumberedWindowArithmeticPairBoundsProof

private theorem hasCandidate {n a b : Nat} (h : pair a b = n) :
    (a,b) ∈ pairCandidates n := by
  have ⟨ha,hb⟩ := components a b
  rw [h] at ha hb
  exact List.mem_flatMap.mpr ⟨a,List.mem_range.mpr (Nat.lt_succ_of_le ha),
    List.mem_map.mpr ⟨b,List.mem_range.mpr (Nat.lt_succ_of_le hb),rfl⟩⟩

private theorem sound {n a b : Nat} (h : decode n = some (a,b)) : pair a b = n := by
  unfold decode at h
  exact of_decide_eq_true (List.find?_some h)

private theorem complete {n a b : Nat} (h : pair a b = n) : decode n = some (a,b) := by
  cases hResult : decode n with
  | none =>
    unfold decode at hResult
    have hAbsent := List.find?_eq_none.mp hResult (a,b) (hasCandidate h)
    exact False.elim (hAbsent (decide_eq_true_eq.mpr h))
  | some p =>
    obtain ⟨c,d⟩ := p
    obtain ⟨rfl,rfl⟩ := (injection a b c d).mp (h.trans (sound hResult).symm)
    rfl

theorem exactDecode : ExactPairDecode :=
  fun _ _ _ => ⟨sound,complete⟩

theorem roundtrip : PairRoundtrip := fun _ _ => complete rfl

theorem exactNonPair : ExactNonPair := by
  intro n
  constructor
  · intro hnone h
    obtain ⟨a,b,h⟩ := h
    have hsome := complete h
    rw [hnone] at hsome
    cases hsome
  · intro h
    cases hResult : decode n with
    | none => rfl
    | some p =>
      obtain ⟨a,b⟩ := p
      exact False.elim (h ⟨a,b,sound hResult⟩)

end LogicLineages.PersistentMarking.NumberedWindowArithmeticPairDecodeProof
