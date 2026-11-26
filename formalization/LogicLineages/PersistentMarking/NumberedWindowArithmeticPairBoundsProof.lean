import LogicLineages.PersistentMarking.NumberedWindowArithmeticPairTargets

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticPairBoundsProof
open NumberedWindowArithmeticPair NumberedWindowArithmeticPairTargets

theorem components : PairComponentBounds := by
  intro a b
  let s := a+b
  have hs : s ≤ s*s := by
    by_cases hz : s = 0
    · rw [hz]; exact Nat.le_refl 0
    · have ho : 1 ≤ s := by omega
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left s ho
  have hb : b ≤ s := by dsimp [s]; omega
  change a ≤ s*s+a ∧ b ≤ s*s+a
  constructor <;> omega

private theorem squareGap {s t : Nat} (h : s < t) : s*s+s < t*t := by
  have hb : s+1 ≤ t := Nat.succ_le_of_lt h
  have hm := Nat.mul_le_mul hb hb
  have he : (s+1)*(s+1) = s*s+s+s+1 := by
    simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one,Nat.one_mul]
    omega
  rw [he] at hm
  omega

theorem injection : ExactPairInjection := by
  intro a b c d
  constructor
  · intro hp
    let s := a+b
    let t := c+d
    have hp' : s*s+a = t*t+c := hp
    have hs : a ≤ s := by dsimp [s]; omega
    have ht : c ≤ t := by dsimp [t]; omega
    have e : s = t := by
      rcases Nat.lt_trichotomy s t with hlt | he | hgt
      · have hg := squareGap hlt
        omega
      · exact he
      · have hg := squareGap hgt
        omega
    rw [e] at hp'
    have ha : a = c := Nat.add_left_cancel hp'
    have hb : b = d := by dsimp [s,t] at e; omega
    exact ⟨ha,hb⟩
  · rintro ⟨rfl,rfl⟩
    rfl

end LogicLineages.PersistentMarking.NumberedWindowArithmeticPairBoundsProof
