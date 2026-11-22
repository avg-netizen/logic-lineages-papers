module
public import LogicLineages.PermittedControl.ActualBitFamilyRawDriverTargets
import LogicLineages.PermittedControl.ActualBitFamilyRawDriverCalibrationProof
import LogicLineages.PermittedControl.ActualBitFamilyExistentialLowZeroProof
import LogicLineages.PermittedControl.ActualNamedBitFamilyCommonCutoffStepProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBitFamilyRawDriver
open OrdinalComparison
open ActualGuardedResidualBitFamily (Family)
open ActualBitFamilyRawLayout (encodeFamily names)
open ActualBitFamilyLowSlices (dimension)
open ActualBitFamilyExistentialLow (Satisfiable closed exactBitFamilyClosed)
open ActualNamedBitFamilyCommonCutoffStep (children exactCommonCutoffNonemptyStep exactCommonCutoffChildrenSmaller)

theorem typedNextSmaller (f : Nat → Nat) (bound : BoundProgram) (fs ch : Family)
    (used : ch ∈ typedNext f bound fs) : dimension ch < dimension fs := by
  unfold typedNext at used
  split at used
  · exact False.elim (List.not_mem_nil used)
  · exact exactCommonCutoffChildrenSmaller f (bound (encodeFamily fs)) fs
      (names (encodeFamily fs)) (exactDriverNames fs) ch used

theorem exactDriverDepth : ExactDriverDepth := by
  intro f bound s limit initial n
  induction n with
  | zero =>
    intro fs used
    simpa only [Nat.add_zero] using initial fs used
  | succ n ih =>
    intro fs used
    change fs ∈ (typedScan f bound s n).2.flatMap (typedNext f bound) at used
    obtain ⟨prior,listed,edge⟩ := List.mem_flatMap.mp used
    have small := typedNextSmaller f bound prior fs edge
    have paid := ih prior listed
    omega

theorem typedAdvanceSound (f : Nat → Nat) (B : Nat) (bound : BoundProgram)
    (high : HighProgram) (chosen : SelectedWithThreshold f B) (cal : Calibrated B bound high)
    (s : TypedState) : Witness f (typedAdvance f bound s) ↔ Witness f s := by
  constructor
  · rintro (done | ⟨child,listed,yes⟩)
    · change (s.1 || s.2.any typedHit) = true at done
      rcases Bool.or_eq_true.mp done with early | found
      · exact Or.inl early
      · obtain ⟨fs,used,good⟩ := List.any_eq_true.mp found
        obtain ⟨empty,value⟩ := Bool.and_eq_true.mp good
        exact Or.inr ⟨fs,used,(exactBitFamilyClosed f fs (of_decide_eq_true empty)).mp value⟩
    · change child ∈ s.2.flatMap (typedNext f bound) at listed
      obtain ⟨fs,used,edge⟩ := List.mem_flatMap.mp listed
      unfold typedNext at edge
      split at edge
      · exact False.elim (List.not_mem_nil edge)
      · rename_i nz
        have positive := Nat.pos_of_ne_zero nz
        have fund := (cal fs positive).1
        exact Or.inr ⟨fs,used,(exactCommonCutoffNonemptyStep f B (bound (encodeFamily fs))
          chosen fs (names (encodeFamily fs)) (exactDriverNames fs) fund positive).mpr ⟨child,edge,yes⟩⟩
  · rintro (done | ⟨fs,used,yes⟩)
    · exact Or.inl (Bool.or_eq_true.mpr (Or.inl done))
    · by_cases empty : dimension fs = 0
      · have found : s.2.any typedHit = true := List.any_eq_true.mpr
          ⟨fs,used,Bool.and_eq_true.mpr ⟨decide_eq_true empty,(exactBitFamilyClosed f fs empty).mpr yes⟩⟩
        exact Or.inl (Bool.or_eq_true.mpr (Or.inr found))
      · have positive := Nat.pos_of_ne_zero empty
        have fund := (cal fs positive).1
        obtain ⟨child,listed,live⟩ :=
          (exactCommonCutoffNonemptyStep f B (bound (encodeFamily fs)) chosen fs
            (names (encodeFamily fs)) (exactDriverNames fs) fund positive).mp yes
        have edge : child ∈ typedNext f bound fs := by
          rw [typedNext,if_neg empty]
          exact listed
        exact Or.inr ⟨child,List.mem_flatMap.mpr ⟨fs,used,edge⟩,live⟩

theorem typedScanSound (f : Nat → Nat) (B : Nat) (bound : BoundProgram)
    (high : HighProgram) (chosen : SelectedWithThreshold f B) (cal : Calibrated B bound high)
    (s : TypedState) (n : Nat) : Witness f (typedScan f bound s n) ↔ Witness f s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Witness f (typedAdvance f bound (typedScan f bound s n)) ↔ Witness f s
    exact (typedAdvanceSound f B bound high chosen cal (typedScan f bound s n)).trans ih

private theorem noLeft (f : Nat → Nat) (bound : BoundProgram) (fs : Family) :
    (typedScan f bound (false,[fs]) (dimension fs + 1)).2 = [] := by
  let st : TypedState := (false,[fs])
  have start : ∀ p ∈ st.2, dimension p ≤ dimension fs := by
    intro p member
    have eq : p = fs := List.mem_singleton.mp member
    subst p
    exact Nat.le_refl _
  cases h : (typedScan f bound (false,[fs]) (dimension fs + 1)).2 with
  | nil => rfl
  | cons hd tl =>
    have used : hd ∈ (typedScan f bound st (dimension fs + 1)).2 := by
      change hd ∈ (typedScan f bound (false,[fs]) (dimension fs + 1)).2
      rw [h]
      exact List.mem_cons_self
    have wrong := exactDriverDepth f bound st (dimension fs) start (dimension fs + 1) hd used
    omega

theorem exactDriverSolve : ExactDriverSolve := by
  intro f B bound high chosen cal fs
  change (scan f bound high (encodeState (false,[fs])) (depth (encodeFamily fs) + 1)).1 = true ↔ _
  rw [exactDriverDepthCode, exactDriverTransport f B bound high cal]
  have path := typedScanSound f B bound high chosen cal (false,[fs]) (dimension fs + 1)
  unfold Witness at path
  rw [noLeft f bound fs] at path
  change (typedScan f bound (false,[fs]) (dimension fs + 1)).1 = true ↔ Satisfiable f fs
  constructor
  · intro yes
    rcases path.mp (Or.inl yes) with wrong | ⟨g,member,live⟩
    · exact False.elim (by cases wrong)
    · have same : g = fs := List.mem_singleton.mp member
      subst g
      exact live
  · intro yes
    rcases path.mpr (Or.inr ⟨fs,List.mem_cons_self,yes⟩) with ok | ⟨g,member,_⟩
    · exact ok
    · exact False.elim (List.not_mem_nil member)

end LogicLineages.PermittedControl.ActualBitFamilyRawDriver
