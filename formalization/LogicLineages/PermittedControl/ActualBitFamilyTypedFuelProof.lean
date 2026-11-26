module
public import LogicLineages.PermittedControl.ActualBitFamilyTypedFuelTargets
import LogicLineages.PermittedControl.ActualBitFamilyExistentialStepProof
import LogicLineages.PermittedControl.ActualBitFamilyExistentialLowZeroProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBitFamilyTypedFuel
open ActualBitFamilyExistentialLow (Satisfiable closed exactBitFamilyClosed)
open ActualBitFamilyExistentialStep (layer children exactNonemptyBitFamilyStep exactSmallerBitFamilyChildren)
open ActualBitFamilyLowSlices (dimension)

theorem exactTypedFuelSound : ExactTypedFuelSound := by
  intro f B chosen n
  induction n with
  | zero =>
    intro family accepted
    by_cases empty : dimension family = 0
    · rw [fuel,if_pos empty] at accepted
      exact (exactBitFamilyClosed f family empty).mp accepted
    · rw [fuel,if_neg empty] at accepted
      cases accepted
  | succ n ih =>
    intro family accepted
    by_cases empty : dimension family = 0
    · rw [fuel,layer,if_pos empty] at accepted
      exact (exactBitFamilyClosed f family empty).mp accepted
    · rw [fuel,layer,if_neg empty] at accepted
      have branch : (children f B family).any (fuel f B n) = true := accepted
      obtain ⟨out,used,yes⟩ := List.any_eq_true.mp branch
      exact (exactNonemptyBitFamilyStep f B chosen family (Nat.pos_of_ne_zero empty)).mpr
        ⟨out,used,ih out yes⟩

theorem exactTypedFuelComplete : ExactTypedFuelComplete := by
  intro f B chosen n
  induction n with
  | zero =>
    intro family enough truth
    have empty : dimension family = 0 := Nat.eq_zero_of_le_zero enough
    rw [fuel,if_pos empty]
    exact (exactBitFamilyClosed f family empty).mpr truth
  | succ n ih =>
    intro family enough truth
    by_cases empty : dimension family = 0
    · rw [fuel,layer,if_pos empty]
      exact (exactBitFamilyClosed f family empty).mpr truth
    · obtain ⟨out,used,smallTruth⟩ :=
        (exactNonemptyBitFamilyStep f B chosen family (Nat.pos_of_ne_zero empty)).mp truth
      have smaller := exactSmallerBitFamilyChildren f B family out used
      have available : dimension out ≤ n := by omega
      rw [fuel,layer,if_neg empty]
      change (children f B family).any (fuel f B n) = true
      exact List.any_eq_true.mpr ⟨out,used,ih out available smallTruth⟩

theorem exactTypedFamilySolve : ExactTypedFamilySolve := by
  intro f B chosen family
  have accepts : solve f B family = true ↔ Satisfiable f family :=
    ⟨exactTypedFuelSound f B chosen (dimension family) family,
      exactTypedFuelComplete f B chosen (dimension family) family le_rfl⟩
  exact ⟨accepts,by cases h : solve f B family <;> simp_all⟩

end LogicLineages.PermittedControl.ActualBitFamilyTypedFuel
