module
public import LogicLineages.OrdinalComparison.SignedPhiSeparationTargets
public import LogicLineages.OrdinalComparison.SignedShiftCollectionDomainProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.SignedPhiSeparation.Proof
open SignedShiftCollection

/-- The domain requirement is retained before any block cancellation. -/
theorem domainOffset_le_delta (row : Row) : domainOffset row ≤ delta row := by
  by_cases h : collected row = []
  · simp only [delta, if_pos h, le_refl]
  · simp only [delta, if_neg h]
    exact le_max_left _ _

theorem delta_of_cancelled (row : Row) (h : collected row = []) :
    delta row = domainOffset row := by
  simp only [delta, if_pos h]

/-- Casting the source algorithm gives the exact integer maximum, even if
A + 1 - B is negative. The nonnegative original domain bound absorbs zero. -/
theorem delta_cast (row : Row) (h : collected row ≠ []) :
    (delta row : Int) = max (domainOffset row : Int)
      ((lowerMass row : Int) + 1 - greatestShift row) := by
  simp only [delta, if_neg h]
  omega

theorem shiftedArgument_safe (row : Row) (a : Int × Int) (ha : a ∈ row)
    (x : Nat) : 0 ≤ (x : Int) + (delta row : Int) + a.2 := by
  have hs := SignedShiftCollection.Proof.domainSafe row a ha
  have hd := domainOffset_le_delta row
  omega

theorem shiftedArgument_cast (row : Row) (a : Int × Int) (ha : a ∈ row)
    (x : Nat) :
    (argument (shiftedInput row x) a.2 : Int) =
      (x : Int) + (delta row : Int) + a.2 := by
  have hs := shiftedArgument_safe row a ha x
  unfold argument shiftedInput
  rw [Int.natCast_add]
  exact Int.toNat_of_nonneg hs

theorem shiftedArgument_rebased (row : Row) (a : Int × Int) (ha : a ∈ row)
    (x : Nat) :
    argument (shiftedInput row x) a.2 = rebasedInput row x + rebaseKey row a.2 := by
  have ha' := shiftedArgument_cast row a ha x
  have hk := SignedShiftCollection.Proof.rebaseKey_cast row a ha
  have hd := domainOffset_le_delta row
  unfold rebasedInput
  omega

/-- Reconstruction at the computed greatest key is exact without requiring
that the key survive. The nonempty target uses it only at the actual leader. -/
theorem greatestArgument_rebased (row : Row) (x : Nat) :
    argument (shiftedInput row x) (greatestShift row) =
      rebasedInput row x + greatestKey row := by
  have hd := domainOffset_le_delta row
  unfold argument shiftedInput greatestShift originalShift rebasedInput
  omega

theorem exactSourceShiftAndArguments : Targets.ExactSourceShiftAndArguments := by
  intro row
  refine ⟨SignedShiftCollection.Proof.domainOffset_le_iff row,
    domainOffset_le_delta row, delta_of_cancelled row, delta_cast row, ?_⟩
  intro a ha x
  exact ⟨shiftedArgument_safe row a ha x, shiftedArgument_cast row a ha x,
    shiftedArgument_rebased row a ha x⟩

end LogicLineages.OrdinalComparison.SignedPhiSeparation.Proof
