module
public import LogicLineages.PermittedControl.ActualNamedBitFamilyCommonCutoffStepTargets
import LogicLineages.PermittedControl.ActualNamedBitFamilyHighAboveExistentialProof
import LogicLineages.PermittedControl.ActualNamedBitFamilyHighAboveDimensionProof
import LogicLineages.PermittedControl.ActualBitFamilyExistentialLowProof
import LogicLineages.PermittedControl.ActualBitFamilyExistentialLowZeroProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualNamedBitFamilyCommonCutoffStep
open ActualGuardedResidualBitFamily (Family)
open ActualBitFamilyLowSlices (coordinates dimension)
open ActualBitFamilyHigh (AllPaid)
open ActualNamedBitFamilyHighAbove (compile exactAboveHighExistential exactAboveHighDimension)
open ActualBitFamilyExistentialLow (exactBitFamilyExistentialLow exactBitFamilyExistentialLowDimension exactBitFamilyClosed)

theorem exactNamedLowChildMembership : ExactNamedLowChildMembership := by
  intro f C family names supplied out
  constructor
  · intro present
    obtain ⟨name,atName,child⟩ := List.mem_flatMap.mp present
    have actual := (supplied.2 name).mp atName
    exact List.mem_flatMap.mpr ⟨name,Finset.mem_toList.mpr actual,child⟩
  · intro present
    obtain ⟨name,atName,child⟩ := List.mem_flatMap.mp present
    have actual := Finset.mem_toList.mp atName
    exact List.mem_flatMap.mpr ⟨name,(supplied.2 name).mpr actual,child⟩

theorem exactCommonCutoffNonemptyStep : ExactCommonCutoffNonemptyStep := by
  intro f B C selected family names supplied large nonempty
  have lo := exactBitFamilyExistentialLow f C family
  have hi := exactAboveHighExistential f B C selected family names supplied large nonempty
  have same := exactNamedLowChildMembership f C family names supplied
  constructor
  · rintro ⟨ρ,truth⟩
    by_cases small : ∃ n ∈ coordinates family, ρ n < C
    · obtain ⟨out,listed,holds⟩ := lo.mp ⟨ρ,small,truth⟩
      exact ⟨out,List.mem_append_left _ ((same out).mpr listed),holds⟩
    · have paid : AllPaid C family ρ :=
        fun n used => Nat.le_of_not_gt (fun below => small ⟨n,used,below⟩)
      obtain ⟨p,listed,lower,truthAt⟩ := hi.mp ⟨ρ,paid,truth⟩
      exact ⟨p.2,List.mem_append_right _ (List.mem_map.mpr ⟨p,listed,rfl⟩),lower,truthAt⟩
  · rintro ⟨out,emitted,truth⟩
    rcases List.mem_append.mp emitted with lower | higher
    · obtain ⟨ρ,_,actual⟩ := lo.mpr ⟨out,(same out).mp lower,truth⟩
      exact ⟨ρ,actual⟩
    · have chart : ∃ p ∈ compile C family names, p.2 = out :=
        List.mem_map.mp (show out ∈ (compile C family names).map Prod.snd from higher)
      obtain ⟨p,listedHigh,sameOut⟩ := chart
      rw [← sameOut] at truth
      obtain ⟨ρ,_,actual⟩ := hi.mpr ⟨p,listedHigh,truth⟩
      exact ⟨ρ,actual⟩

theorem exactCommonCutoffChildrenSmaller : ExactCommonCutoffChildrenSmaller := by
  intro f C family names supplied out emitted
  rcases List.mem_append.mp emitted with lower | higher
  · exact exactBitFamilyExistentialLowDimension f C family out
      ((exactNamedLowChildMembership f C family names supplied out).mp lower)
  · have chart : ∃ p ∈ compile C family names, p.2 = out :=
      List.mem_map.mp (show out ∈ (compile C family names).map Prod.snd from higher)
    obtain ⟨p,listedHigh,sameOut⟩ := chart
    rw [← sameOut]
    exact (exactAboveHighDimension C family names supplied p listedHigh).2

theorem exactCommonCutoffLayer : ExactCommonCutoffLayer := by
  intro f B C selected family names supplied large
  by_cases zero : dimension family = 0
  · rw [layer,if_pos zero]
    exact exactBitFamilyClosed f family zero
  · rw [layer,if_neg zero]
    exact (exactCommonCutoffNonemptyStep f B C selected family names supplied large (Nat.pos_of_ne_zero zero)).symm

end LogicLineages.PermittedControl.ActualNamedBitFamilyCommonCutoffStep
