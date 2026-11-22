module
public import LogicLineages.PermittedControl.ActualBitFamilyRawSemanticDriverTargets
import LogicLineages.PermittedControl.ActualBitFamilyRawDriverCalibrationProof
import LogicLineages.PermittedControl.ActualBitFamilyRawLowProof
import LogicLineages.PermittedControl.ActualNamedBitFamilyCommonCutoffStepProof
import LogicLineages.PermittedControl.ActualBitFamilyExistentialLowProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBitFamilyRawSemanticDriver
open ActualBitFamilyRawDriver (BoundProgram HighProgram nextCode lowCode exactDriverDepthCode exactDriverNames)
open ActualBitFamilyRawLayout (encodeFamily names)
open ActualBitFamilyRawLow (stripsCode exactRawLowCalibration)
open ActualGuardedResidualBitFamily (Family Holds)
open ActualBitFamilyLowSlices (strips coordinates dimension)
open ActualBitFamilyExistentialLow (Satisfiable exactBitFamilyExistentialLow exactBitFamilyExistentialLowDimension)
open ActualBitFamilyHigh (AllPaid)
open ActualNamedBitFamilyCommonCutoffStep (low exactNamedLowChildMembership)

private theorem encodedLow (f : Nat → Nat) (C : Nat) (fs : Family) (ns : List Nat) :
    ns.flatMap (fun k => (stripsCode f (k,C,encodeFamily fs)).map Prod.snd) =
      (low f C fs ns).map encodeFamily := by
  induction ns with
  | nil => rfl
  | cons k ks ih =>
    have eq := exactRawLowCalibration.2.2 f k C fs
    change
      (stripsCode f (k,C,encodeFamily fs)).map Prod.snd ++
        ks.flatMap (fun k => (stripsCode f (k,C,encodeFamily fs)).map Prod.snd) =
      ((strips f k C fs).map Prod.snd ++ low f C fs ks).map encodeFamily
    rw [eq,ih,List.map_append]
    simp only [List.map_map,Function.comp_def]

theorem exactSemanticDriverStep : ExactSemanticDriverStep := by
  intro f B bound high choose cert fs
  by_cases empty : dimension fs = 0
  · rw [nextCode,exactDriverDepthCode,if_pos empty,next,if_pos empty]
    refine ⟨rfl,?_,?_⟩
    · intro ch bad
      exact False.elim (List.not_mem_nil bad)
    · intro bad
      omega
  · have positive := Nat.pos_of_ne_zero empty
    have rawHigh := (cert fs positive).2.1
    have smaller := (cert fs positive).2.2.1
    have paidHigh := (cert fs positive).2.2.2
    have lo := exactBitFamilyExistentialLow f (bound (encodeFamily fs)) fs
    have named := exactNamedLowChildMembership f (bound (encodeFamily fs)) fs
      (names (encodeFamily fs)) (exactDriverNames fs)
    rw [next,if_neg empty]
    refine ⟨?_,?_,?_⟩
    · rw [nextCode,exactDriverDepthCode,if_neg empty]
      change lowCode f (bound (encodeFamily fs)) (encodeFamily fs) ++
        high (bound (encodeFamily fs),encodeFamily fs) =
        (low f (bound (encodeFamily fs)) fs (names (encodeFamily fs)) ++ choose fs).map encodeFamily
      rw [rawHigh,List.map_append]
      exact congrArg (fun base => base ++ (choose fs).map encodeFamily)
        (encodedLow f (bound (encodeFamily fs)) fs (names (encodeFamily fs)))
    · intro ch present
      rcases List.mem_append.mp present with found | found
      · exact exactBitFamilyExistentialLowDimension f (bound (encodeFamily fs)) fs ch
          ((named ch).mp found)
      · exact smaller ch found
    · intro _
      constructor
      · rintro ⟨ρ,truth⟩
        by_cases small : ∃ n ∈ coordinates fs, ρ n < bound (encodeFamily fs)
        · obtain ⟨out,listed,live⟩ := lo.mp ⟨ρ,small,truth⟩
          exact ⟨out,List.mem_append_left _ ((named out).mpr listed),live⟩
        · have paid : AllPaid (bound (encodeFamily fs)) fs ρ :=
            fun n used => Nat.le_of_not_gt (fun below => small ⟨n,used,below⟩)
          obtain ⟨out,listed,live⟩ := paidHigh.mp ⟨ρ,paid,truth⟩
          exact ⟨out,List.mem_append_right _ listed,live⟩
      · rintro ⟨out,listed,live⟩
        rcases List.mem_append.mp listed with lower | upper
        · obtain ⟨ρ,_,truth⟩ := lo.mpr ⟨out,(named out).mp lower,live⟩
          exact ⟨ρ,truth⟩
        · obtain ⟨ρ,_,truth⟩ := paidHigh.mpr ⟨out,upper,live⟩
          exact ⟨ρ,truth⟩

end LogicLineages.PermittedControl.ActualBitFamilyRawSemanticDriver
