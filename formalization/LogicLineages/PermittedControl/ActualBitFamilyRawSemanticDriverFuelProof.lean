module
public import LogicLineages.PermittedControl.ActualBitFamilyRawSemanticDriverTargets
import LogicLineages.PermittedControl.ActualBitFamilyRawSemanticDriverStepProof
import LogicLineages.PermittedControl.ActualBitFamilyRawDriverCalibrationProof
import LogicLineages.PermittedControl.ActualBitFamilyRawClosedProof
import LogicLineages.PermittedControl.ActualBitFamilyExistentialLowZeroProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBitFamilyRawSemanticDriver
open ActualBitFamilyRawDriver (BoundProgram HighProgram TypedState State Witness typedHit scan advance hit nextCode encodeState solve depth exactDriverDepthCode)
open ActualBitFamilyRawLayout (encodeFamily)
open ActualBitFamilyRawClosed (exactClosedRawCalibration)
open ActualGuardedResidualBitFamily (Family)
open ActualBitFamilyExistentialLow (Satisfiable exactBitFamilyClosed)
open ActualBitFamilyLowSlices (dimension)

private def advanceWith (step : Family → List Family) (s : TypedState) : TypedState :=
  (s.1 || s.2.any typedHit,s.2.flatMap step)

private def scanWith (step : Family → List Family) (s : TypedState) (n : Nat) : TypedState :=
  Nat.rec s (fun _ t => advanceWith step t) n

private theorem hitExact (fs : Family) : hit (encodeFamily fs) = typedHit fs := by
  simp only [hit,typedHit,exactDriverDepthCode,exactClosedRawCalibration.2]

private theorem encodedAdvance (f : Nat → Nat) (bound : BoundProgram) (high : HighProgram)
    (step : Family → List Family) (cal : ∀ fs, nextCode f bound high (encodeFamily fs) = (step fs).map encodeFamily)
    (s : TypedState) : advance f bound high (encodeState s) = encodeState (advanceWith step s) := by
  rcases s with ⟨answer,fs⟩
  change (answer || (fs.map encodeFamily).any hit,
      (fs.map encodeFamily).flatMap (nextCode f bound high)) =
    (answer || fs.any typedHit,(fs.flatMap step).map encodeFamily)
  have children : (fs.map encodeFamily).flatMap (nextCode f bound high) =
      (fs.flatMap step).map encodeFamily := by
    induction fs with
    | nil => rfl
    | cons a tail ih =>
      simp only [List.map_cons,List.flatMap_cons,List.map_append,cal,ih]
  have answerBit : (fs.map encodeFamily).any hit = fs.any typedHit := by
    clear children
    induction fs with
    | nil => rfl
    | cons a tail ih => simp only [List.map_cons,List.any_cons,hitExact,ih]
  rw [answerBit,children]

private theorem encodedScan (f : Nat → Nat) (bound : BoundProgram) (high : HighProgram)
    (step : Family → List Family) (cal : ∀ fs, nextCode f bound high (encodeFamily fs) = (step fs).map encodeFamily)
    (s : TypedState) (n : Nat) : scan f bound high (encodeState s) n = encodeState (scanWith step s n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change advance f bound high (scan f bound high (encodeState s) n) =
      encodeState (advanceWith step (scanWith step s n))
    rw [ih, encodedAdvance f bound high step cal]

private theorem advanceWitness (f : Nat → Nat) (step : Family → List Family)
    (zero : ∀ fs, dimension fs = 0 → step fs = [])
    (splitSat : ∀ fs, 0 < dimension fs →
      (Satisfiable f fs ↔ ∃ ch ∈ step fs, Satisfiable f ch))
    (s : TypedState) : Witness f (advanceWith step s) ↔ Witness f s := by
  constructor
  · rintro (done | ⟨ch,listed,live⟩)
    · change (s.1 || s.2.any typedHit) = true at done
      rcases Bool.or_eq_true_iff.mp done with found | scanned
      · exact Or.inl found
      · obtain ⟨fs,used,val⟩ := List.any_eq_true.mp scanned
        obtain ⟨blank,bit⟩ := Bool.and_eq_true_iff.mp val
        exact Or.inr ⟨fs,used,(exactBitFamilyClosed f fs (of_decide_eq_true blank)).mp bit⟩
    · change ch ∈ s.2.flatMap step at listed
      obtain ⟨fs,used,edge⟩ := List.mem_flatMap.mp listed
      by_cases empty : dimension fs = 0
      · rw [zero fs empty] at edge
        exact False.elim (List.not_mem_nil edge)
      · exact Or.inr ⟨fs,used,(splitSat fs (Nat.pos_of_ne_zero empty)).mpr ⟨ch,edge,live⟩⟩
  · rintro (done | ⟨fs,used,live⟩)
    · exact Or.inl (Bool.or_eq_true_iff.mpr (Or.inl done))
    · by_cases empty : dimension fs = 0
      · have found : s.2.any typedHit = true := List.any_eq_true.mpr
          ⟨fs,used,Bool.and_eq_true_iff.mpr ⟨decide_eq_true empty,(exactBitFamilyClosed f fs empty).mpr live⟩⟩
        exact Or.inl (Bool.or_eq_true_iff.mpr (Or.inr found))
      · obtain ⟨ch,edge,yes⟩ := (splitSat fs (Nat.pos_of_ne_zero empty)).mp live
        exact Or.inr ⟨ch,List.mem_flatMap.mpr ⟨fs,used,edge⟩,yes⟩

private theorem scanWitness (f : Nat → Nat) (step : Family → List Family)
    (zero : ∀ fs, dimension fs = 0 → step fs = [])
    (splitSat : ∀ fs, 0 < dimension fs →
      (Satisfiable f fs ↔ ∃ ch ∈ step fs, Satisfiable f ch))
    (s : TypedState) (n : Nat) : Witness f (scanWith step s n) ↔ Witness f s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Witness f (advanceWith step (scanWith step s n)) ↔ Witness f s
    exact (advanceWitness f step zero splitSat (scanWith step s n)).trans ih

private theorem scanDepth (step : Family → List Family)
    (small : ∀ fs ch, ch ∈ step fs → dimension ch < dimension fs)
    (s : TypedState) (d : Nat) (init : ∀ fs ∈ s.2, dimension fs ≤ d) (n : Nat) :
    ∀ ch ∈ (scanWith step s n).2, dimension ch + n ≤ d := by
  induction n with
  | zero =>
    intro ch used
    simpa only [Nat.add_zero] using init ch used
  | succ n ih =>
    intro ch used
    change ch ∈ (scanWith step s n).2.flatMap step at used
    obtain ⟨fs,listed,edge⟩ := List.mem_flatMap.mp used
    have h := small fs ch edge
    have k := ih fs listed
    omega

private theorem scanEmpty (step : Family → List Family)
    (small : ∀ fs ch, ch ∈ step fs → dimension ch < dimension fs)
    (fs : Family) : (scanWith step (false,[fs]) (dimension fs + 1)).2 = [] := by
  let st : TypedState := (false,[fs])
  have init : ∀ ch ∈ st.2, dimension ch ≤ dimension fs := by
    intro ch used
    have eq : ch = fs := List.mem_singleton.mp used
    subst ch
    exact Nat.le_refl _
  cases same : (scanWith step (false,[fs]) (dimension fs + 1)).2 with
  | nil => rfl
  | cons hd tl =>
    have used : hd ∈ (scanWith step st (dimension fs + 1)).2 := by
      change hd ∈ (scanWith step (false,[fs]) (dimension fs + 1)).2
      rw [same]
      exact List.mem_cons_self
    have wrong := scanDepth step small st (dimension fs) init (dimension fs + 1) hd used
    omega

theorem exactSemanticDriverSolve : ExactSemanticDriverSolve := by
  intro f B bound high choose cert fs
  let step := next f bound choose
  have certStep (g : Family) := exactSemanticDriverStep f B bound high choose cert g
  have zero (g : Family) (blank : dimension g = 0) : step g = [] := by
    show next f bound choose g = []
    rw [next,if_pos blank]
  change (scan f bound high (encodeState (false,[fs])) (depth (encodeFamily fs) + 1)).1 = true ↔ _
  rw [exactDriverDepthCode, encodedScan f bound high step (fun g => (certStep g).1)]
  have path := scanWitness f step zero (fun g => (certStep g).2.2) (false,[fs]) (dimension fs + 1)
  unfold Witness at path
  rw [scanEmpty step (fun g ch => (certStep g).2.1 ch) fs] at path
  change (scanWith step (false,[fs]) (dimension fs + 1)).1 = true ↔ Satisfiable f fs
  constructor
  · intro yes
    rcases path.mp (Or.inl yes) with wrong | ⟨g,used,ok⟩
    · exact False.elim (by cases wrong)
    · have eq : g = fs := List.mem_singleton.mp used
      subst g
      exact ok
  · intro yes
    rcases path.mpr (Or.inr ⟨fs,List.mem_cons_self,yes⟩) with ok | ⟨g,used,_⟩
    · exact ok
    · exact False.elim (List.not_mem_nil used)

end LogicLineages.PermittedControl.ActualBitFamilyRawSemanticDriver
