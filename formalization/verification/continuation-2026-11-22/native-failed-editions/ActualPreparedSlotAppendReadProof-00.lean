module
public import LogicLineages.PermittedControl.ActualPreparedSlotAppendTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualPreparedSlotAppend
open PreparedProjection

private theorem leftBound (left right : List LowerOperand) (j : Nat) (h : j < left.length) :
    j < (left ++ right).length := by simp only [List.length_append]; omega

private theorem rightBound (left right : List LowerOperand) (j : Nat) (h : j < right.length) :
    left.length + j < (left ++ right).length := by simp only [List.length_append]; omega

theorem leftAt (left right : List LowerOperand) (j : Nat) (h : j < left.length)
    {hab : j < (left ++ right).length} :
    (left ++ right)[j] = left[j] := List.getElem_append_left h

theorem rightAt (left right : List LowerOperand) (j : Nat) (h : j < right.length)
    {hab : left.length+j < (left ++ right).length} :
    (left ++ right)[left.length+j] = right[j] := by
  rw [List.getElem_append_right (Nat.le_add_right left.length j)]
  simp only [Nat.add_sub_cancel_left]

theorem mergeLeft (d : Nat) (ν₁ ν₂ : Nat → Nat) (n : Nat) (h : n ≤ d) :
    merge d ν₁ ν₂ n = ν₁ n := by simp only [merge,if_pos h]

theorem mergeRight (d : Nat) (ν₁ ν₂ : Nat → Nat) (n : Nat) (positive : 0 < n) :
    view d (merge d ν₁ ν₂) n = ν₂ n := by
  cases n with
  | zero => exact False.elim (Nat.not_lt_zero _ positive)
  | succ j =>
      change merge d ν₁ ν₂ (d+(j+1)) = ν₂ (j+1)
      simp only [merge,if_neg (show ¬ d+(j+1) ≤ d by omega),Nat.add_sub_cancel_left]

private theorem tiedAppend (f ρ : Nat → Nat) (top : Nat) (left right : List LowerOperand)
    (ν : Nat → Nat) :
    PreparedTableTied f top ρ (left ++ right) ν ↔
      PreparedTableTied f top ρ left ν ∧ PreparedTableTied f top ρ right (view left.length ν) := by
  constructor
  · intro both
    constructor
    · intro j hj
      have used := leftBound left right j hj
      have h := both j used
      change (left ++ right)[j].rank < top ∧ LowerOperandActual f ρ (left ++ right)[j] (ν (j+1)) at h
      rw [leftAt left right j hj] at h
      exact h
    · intro j hj
      have used := rightBound left right j hj
      have h := both (left.length+j) used
      change (left ++ right)[left.length+j].rank < top ∧
        LowerOperandActual f ρ (left ++ right)[left.length+j] (ν ((left.length+j)+1)) at h
      rw [rightAt left right j hj] at h
      change right[j].rank < top ∧ LowerOperandActual f ρ right[j] (view left.length ν (j+1))
      simpa only [view,shiftName,Nat.add_assoc] using h
  · rintro ⟨a,b⟩ k bound
    by_cases atLeft : k < left.length
    · change (left ++ right)[k].rank < top ∧ LowerOperandActual f ρ (left ++ right)[k] (ν (k+1))
      rw [leftAt left right k atLeft]
      exact a k atLeft
    · let j := k-left.length
      have atRight : j < right.length := by
        have len := List.length_append left right
        dsimp [j]
        omega
      have eq : k = left.length+j := by dsimp [j]; omega
      have h (k' : Nat) (used : k' < (left ++ right).length) :
          k' = left.length+j →
            (left ++ right)[k'].rank < top ∧
            LowerOperandActual f ρ (left ++ right)[k'] (ν (k'+1)) := by
        intro eq'
        subst k'
        rw [rightAt left right j atRight]
        have original := b j atRight
        change right[j].rank < top ∧ LowerOperandActual f ρ right[j] (view left.length ν (j+1)) at original
        simpa only [view,shiftName,Nat.add_assoc] using original
      exact h k bound eq

theorem exactAppendedReads : ExactAppendedReads := by
  intro f ρ top left right
  refine ⟨?_,?_,tiedAppend f ρ top left right,?_⟩
  · intro j h
    have used := leftBound left right j h
    have literal : (left ++ right)[j] = left[j] := leftAt left right j h
    exact ⟨used,literal,congrArg (lowerOperandRead f ρ) literal⟩
  · intro j h
    have used := rightBound left right j h
    have literal : (left ++ right)[left.length+j] = right[j] := rightAt left right j h
    exact ⟨used,literal,congrArg (lowerOperandRead f ρ) literal⟩
  · intro ν₁ ν₂ h₁ h₂
    apply (tiedAppend f ρ top left right (merge left.length ν₁ ν₂)).mpr
    constructor
    · intro j hj
      have same := mergeLeft left.length ν₁ ν₂ (j+1) (Nat.succ_le_of_lt hj)
      change left[j].rank < top ∧ LowerOperandActual f ρ left[j] (merge left.length ν₁ ν₂ (j+1))
      rw [same]
      exact h₁ j hj
    · intro j hj
      have same := mergeRight left.length ν₁ ν₂ (j+1) (Nat.succ_pos j)
      change right[j].rank < top ∧
        LowerOperandActual f ρ right[j] (view left.length (merge left.length ν₁ ν₂) (j+1))
      rw [same]
      exact h₂ j hj

end LogicLineages.PermittedControl.ActualPreparedSlotAppend
