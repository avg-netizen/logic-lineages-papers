module
public import LogicLineages.PersistentMarking.NumberedWindowPairAlgorithm
public import Mathlib.Data.Nat.Sqrt

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowSparseFloorArithmeticProof
open NumberedWindowPairAlgorithm (pair candidates decode)

def floorDecode (n : Nat) : Option (Nat × Nat) :=
  let s := Nat.sqrt n
  let r := n - s*s
  if r ≤ s then some (r,s-r) else none

private theorem rootOfPair (x y : Nat) : Nat.sqrt (pair x y) = x+y := by
  let s := x+y
  symm
  apply Nat.eq_sqrt.mpr
  change s*s ≤ s*s+x ∧ s*s+x < (s+1)*(s+1)
  constructor
  · exact Nat.le_add_right _ _
  · have hx : x ≤ s := Nat.le_add_right x y
    have hs : (s+1)*(s+1) = s*s+s+s+1 := by
      simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul]
      omega
    rw [hs]
    omega

private theorem components (x y : Nat) : x ≤ pair x y ∧ y ≤ pair x y := by
  let s := x+y
  have hs : s ≤ s*s := by
    by_cases h : s = 0
    · rw [h]
    · have one : 1 ≤ s := by omega
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left s one
  have hx : x ≤ s := Nat.le_add_right x y
  have hy : y ≤ s := by dsimp [s]; omega
  change x ≤ s*s+x ∧ y ≤ s*s+x
  constructor <;> omega

private theorem injective {x y a b : Nat} (h : pair x y = pair a b) : x = a ∧ y = b := by
  have sums := congrArg Nat.sqrt h
  rw [rootOfPair,rootOfPair] at sums
  change (x+y)*(x+y)+x = (a+b)*(a+b)+a at h
  rw [sums] at h
  have left := Nat.add_left_cancel h
  exact ⟨left,by omega⟩

private theorem decodeSound {n x y : Nat} (h : decode n = some (x,y)) : pair x y = n := by
  unfold decode at h
  exact of_decide_eq_true (List.find?_some (p := fun p : Nat × Nat => decide (pair p.1 p.2 = n)) h)

private theorem candidateOfPair {n x y : Nat} (h : pair x y = n) : (x,y) ∈ candidates n := by
  have ⟨hx,hy⟩ := components x y
  rw [h] at hx hy
  exact List.mem_flatMap.mpr ⟨x,List.mem_range.mpr (Nat.lt_succ_of_le hx),
    List.mem_map.mpr ⟨y,List.mem_range.mpr (Nat.lt_succ_of_le hy),rfl⟩⟩

private theorem decodeComplete {n x y : Nat} (h : pair x y = n) : decode n = some (x,y) := by
  cases value : decode n with
  | none =>
    unfold decode at value
    have missed := List.find?_eq_none.mp value (x,y) (candidateOfPair h)
    exact False.elim (missed (decide_eq_true_eq.mpr h))
  | some both =>
    obtain ⟨a,b⟩ := both
    obtain ⟨rfl,rfl⟩ := injective (h.trans (decodeSound value).symm)
    rfl

/-- Exact equality of the floor-residual selector and the existing literal
bounded search. The proof covers every gap in the sparse arithmetic range. -/
theorem floorAgrees (n : Nat) : floorDecode n = decode n := by
  let s := Nat.sqrt n
  let r := n - s*s
  have rootBound : s*s ≤ n := Nat.sqrt_le n
  change (if r ≤ s then some (r,s-r) else none) = _
  by_cases h : r ≤ s
  · have hp : pair r (s-r) = n := by
      unfold pair
      rw [Nat.add_sub_of_le h]
      exact Nat.add_sub_of_le rootBound
    simp [h,decodeComplete hp]
  · have hd : decode n = none := by
      cases value : decode n with
      | none => rfl
      | some both =>
        obtain ⟨x,y⟩ := both
        have hp := decodeSound value
        have hs : s = x+y := by
          change Nat.sqrt n = _
          rw [← hp,rootOfPair]
        have hr : r = x := by
          change n-s*s = x
          rw [← hp,hs]
          simp [pair]
        exact False.elim (h (by rw [hr,hs]; exact Nat.le_add_right _ _))
    simp [h,hd]

end LogicLineages.PersistentMarking.NumberedWindowSparseFloorArithmeticProof
