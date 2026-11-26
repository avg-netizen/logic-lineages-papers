module
public import LogicLineages.PersistentMarking.NumberedWindowFieldAlgorithm
import LogicLineages.PersistentMarking.NumberedWindowSparseFloorArithmeticProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserRawPairProof
open NumberedWindowPairAlgorithm (pair decode)
open NumberedWindowSparseFloorArithmeticProof (floorDecode floorAgrees)

theorem decodedPair {n h t : Nat} (found : decode n = some (h,t)) : pair h t = n := by
  unfold decode at found
  exact of_decide_eq_true
    (List.find?_some (p := fun p : Nat × Nat => decide (pair p.1 p.2 = n)) found)

theorem tailBound (h t : Nat) : t ≤ pair h t := by
  let s := h+t
  have hs : s ≤ s*s := by
    by_cases z : s = 0
    · rw [z]
    · have one : 1 ≤ s := Nat.pos_of_ne_zero z
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left s one
  have ht : t ≤ s := by dsimp [s]; omega
  exact ht.trans (hs.trans (Nat.le_add_right _ _))

private theorem pairRoot (h t : Nat) : Nat.sqrt (pair h t) = h+t := by
  let s := h+t
  symm
  apply Nat.eq_sqrt.mpr
  change s*s ≤ s*s+h ∧ s*s+h < (s+1)*(s+1)
  constructor
  · exact Nat.le_add_right _ _
  · have hh : h ≤ s := Nat.le_add_right h t
    have hs : (s+1)*(s+1) = s*s+s+s+1 := by
      simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul]
      omega
    rw [hs]
    omega

theorem encodedPair (h t : Nat) : decode (pair h t) = some (h,t) := by
  rw [← floorAgrees, floorDecode, pairRoot]
  have remainder : pair h t - (h+t)*(h+t) = h := by simp [pair]
  rw [remainder, if_pos (Nat.le_add_right h t)]
  simp

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserRawPairProof
