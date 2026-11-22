module
public import LogicLineages.PermittedControl.ActualBitFamilyExistentialStepTargets
import LogicLineages.PermittedControl.ActualBitFamilyExistentialLowProof
import LogicLineages.PermittedControl.ActualBitFamilyExistentialLowZeroProof
import LogicLineages.PermittedControl.ActualBitFamilyHighExistentialProof
import LogicLineages.PermittedControl.ActualBitFamilyHighDimensionProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBitFamilyExistentialStep
open ActualBitFamilyExistentialLow (Satisfiable exactBitFamilyExistentialLow exactBitFamilyExistentialLowDimension
  exactBitFamilyClosed)
open ActualBitFamilyHigh (AllPaid cutoff compile exactGenericHighExistential exactGenericHighDimension)
open ActualBitFamilyLowSlices (coordinates dimension)
open ActualGuardedResidualBitFamily (Family Holds)

theorem exactNonemptyBitFamilyStep : ExactNonemptyBitFamilyStep := by
  intro f B chosen family used
  let bound := cutoff B family
  have low := exactBitFamilyExistentialLow f bound family
  have high := exactGenericHighExistential f B chosen family used
  constructor
  · rintro ⟨ρ,truth⟩
    by_cases small : ∃ n ∈ coordinates family, ρ n < bound
    · obtain ⟨out,member,holds⟩ := low.mp ⟨ρ,small,truth⟩
      exact ⟨out,List.mem_append_left _ member,holds⟩
    · have paid : AllPaid bound family ρ :=
        fun n used => Nat.le_of_not_gt (fun below => small ⟨n,used,below⟩)
      obtain ⟨p,member,lower,truth⟩ := high.mp ⟨ρ,paid,truth⟩
      exact ⟨p.2,List.mem_append_right _ (List.mem_map.mpr ⟨p,member,rfl⟩),lower,truth⟩
  · rintro ⟨out,member,truth⟩
    rcases List.mem_append.mp member with small | large
    · obtain ⟨ρ,_,source⟩ := low.mpr ⟨out,small,truth⟩
      exact ⟨ρ,source⟩
    · have src : ∃ p ∈ compile B family, p.2 = out :=
        List.mem_map.mp (show out ∈ (compile B family).map Prod.snd from large)
      obtain ⟨p,member,eq⟩ := src
      subst out
      obtain ⟨ρ,_,source⟩ := high.mpr ⟨p,member,truth⟩
      exact ⟨ρ,source⟩

theorem exactSmallerBitFamilyChildren : ExactSmallerBitFamilyChildren := by
  intro f B family out member
  rcases List.mem_append.mp member with low | high
  · exact exactBitFamilyExistentialLowDimension f (cutoff B family) family out low
  · have src : ∃ p ∈ compile B family, p.2 = out :=
      List.mem_map.mp (show out ∈ (compile B family).map Prod.snd from high)
    obtain ⟨p,member,eq⟩ := src
    subst out
    exact (exactGenericHighDimension B family p member).2

theorem exactSoundBitFamilyLayer : ExactSoundBitFamilyLayer := by
  intro f B chosen family
  by_cases empty : dimension family = 0
  · rw [layer,if_pos empty]
    exact exactBitFamilyClosed f family empty
  · rw [layer,if_neg empty]
    exact (exactNonemptyBitFamilyStep f B chosen family (Nat.pos_of_ne_zero empty)).symm

end LogicLineages.PermittedControl.ActualBitFamilyExistentialStep
