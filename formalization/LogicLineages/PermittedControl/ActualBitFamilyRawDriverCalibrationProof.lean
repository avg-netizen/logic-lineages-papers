module
public import LogicLineages.PermittedControl.ActualBitFamilyRawDriverTargets
import LogicLineages.PermittedControl.ActualBitFamilyRawClosedProof
import LogicLineages.PermittedControl.ActualBitFamilyRawLayoutProof
import LogicLineages.PermittedControl.ActualBitFamilyRawLowProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBitFamilyRawDriver
open ActualGuardedResidualBitFamily (Family)
open ActualBitFamilyRawClosed (exactClosedRawCalibration)
open ActualBitFamilyRawLayout (RawFamily encodeFamily names exactRawFamilyNames)
open ActualBitFamilyRawLow (stripsCode exactRawLowCalibration)
open ActualBitFamilyLowSlices (strips dimension)
open ActualNamedBitFamilyHigh (Supplied)
open ActualNamedBitFamilyCommonCutoffStep (low children)

theorem exactDriverDepthCode (fs : Family) : depth (encodeFamily fs) = dimension fs :=
  (exactRawFamilyNames.2 fs).2

theorem exactDriverNames (fs : Family) : Supplied fs (names (encodeFamily fs)) := by
  refine ⟨(exactRawFamilyNames.1 _).2.1,?_⟩
  intro k
  rw [← (exactRawFamilyNames.2 fs).1, List.mem_toFinset]

private theorem mapLow (f : Nat → Nat) (C : Nat) (fs : Family) (ns : List Nat) :
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
    rw [eq, ih, List.map_append]
    simp only [List.map_map, Function.comp_def]

private theorem nextExact (f : Nat → Nat) (B : Nat) (bound : BoundProgram)
    (high : HighProgram) (cal : Calibrated B bound high) (fs : Family) :
    nextCode f bound high (encodeFamily fs) = (typedNext f bound fs).map encodeFamily := by
  unfold nextCode typedNext
  rw [exactDriverDepthCode]
  split
  · rfl
  · rename_i nz
    have same := (cal fs (Nat.pos_of_ne_zero nz)).2
    rw [same]
    change
      (names (encodeFamily fs)).flatMap
        (fun k => (stripsCode f (k,bound (encodeFamily fs),encodeFamily fs)).map Prod.snd) ++ _ =
      (low f (bound (encodeFamily fs)) fs (names (encodeFamily fs)) ++ _).map encodeFamily
    rw [List.map_append, mapLow]

private theorem hitExact (fs : Family) : hit (encodeFamily fs) = typedHit fs := by
  simp only [hit,typedHit,exactDriverDepthCode,exactClosedRawCalibration.2]

private theorem advanceExact (f : Nat → Nat) (B : Nat) (bound : BoundProgram)
    (high : HighProgram) (cal : Calibrated B bound high) (s : TypedState) :
    advance f bound high (encodeState s) = encodeState (typedAdvance f bound s) := by
  rcases s with ⟨answer,fs⟩
  change
    (answer || (fs.map encodeFamily).any hit,
      (fs.map encodeFamily).flatMap (nextCode f bound high)) =
      (answer || fs.any typedHit,(fs.flatMap (typedNext f bound)).map encodeFamily)
  have hitList : (fs.map encodeFamily).any hit = fs.any typedHit := by
    induction fs with
    | nil => rfl
    | cons a tail ih =>
      simp only [List.map_cons,List.any_cons,hitExact,ih]
  have stepList :
      (fs.map encodeFamily).flatMap (nextCode f bound high) =
        (fs.flatMap (typedNext f bound)).map encodeFamily := by
    induction fs with
    | nil => rfl
    | cons a tail ih =>
      simp only [List.map_cons,List.flatMap_cons,List.map_append,nextExact f B bound high cal,ih]
  rw [hitList,stepList]

theorem exactDriverTransport : ExactDriverTransport := by
  intro f B bound high cal s n
  induction n with
  | zero => rfl
  | succ n ih =>
    change advance f bound high (scan f bound high (encodeState s) n) =
      encodeState (typedAdvance f bound (typedScan f bound s n))
    rw [ih, advanceExact f B bound high cal]

end LogicLineages.PermittedControl.ActualBitFamilyRawDriver
