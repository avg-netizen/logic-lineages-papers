module
public import LogicLineages.PermittedControl.OriginalPrintedTerminalBitClausesTargets
import LogicLineages.PermittedControl.OriginalPrintedTerminalBitClausesBitsProof
import LogicLineages.PermittedControl.OriginalNormalizedMatrixPositiveSnapshotsProof
import LogicLineages.PermittedControl.OriginalPlainTerminalMatrixProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedTerminalBitClauses
open HeterogeneousSignedMatrixSlice (Row Snapshot actualRows)
open OriginalNormalizedMatrixPositiveSnapshots (AllTrue exactPositiveCircuitSnapshots)
open OriginalNormalizedCircuitMatrix (passingList)
open OriginalPrintedPlainMatrixInfiniteLow (circuit)
open OriginalPlainTerminalMatrix (exactPlainTerminalSuffix)

private theorem snapshotLength (f ρ : Nat → Nat) (rows : List Row) (snap : Snapshot)
    (h : actualRows f ρ rows snap) : snap.length = rows.length := by
  induction rows generalizing snap with
  | nil =>
    cases snap with
    | nil => rfl
    | cons v vs => exact False.elim h
  | cons r rs ih =>
    cases snap with
    | nil => exact False.elim h
    | cons v vs => exact congrArg Nat.succ (ih vs h.2.2.2)

private theorem allTrueBits (snap : Snapshot) : AllTrue snap ↔ snap.map Prod.snd = List.replicate snap.length true := by
  induction snap with
  | nil =>
    exact ⟨fun _ => rfl,fun _ v used => False.elim (List.not_mem_nil used)⟩
  | cons x xs ih =>
    constructor
    · intro truth
      exact congrArg₂ List.cons (truth x List.mem_cons_self)
        (ih.mp (fun v used => truth v (List.mem_cons_of_mem _ used)))
    · intro bits
      have frames : x.2 :: xs.map Prod.snd = true :: List.replicate xs.length true := bits
      have tail := ih.mpr (List.cons.inj frames).2
      intro v used
      rcases List.mem_cons.mp used with same | more
      · subst v
        exact (List.cons.inj frames).1
      · exact tail v more

private theorem positiveZip (rows : List Row) :
    zipBits rows (List.replicate rows.length true) = rows.map (fun r => (r,true)) := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    change (r,true) :: zipBits rs (List.replicate rs.length true) = _
    rw [ih] <;> rfl

private theorem positiveTape (f ρ : Nat → Nat) (rows : List Row) :
    ClauseHolds f ρ (rows.map (fun r => (r,true))) ↔
      ∃ snap : Snapshot, actualRows f ρ rows snap ∧ AllTrue snap := by
  have h := exactBitTape f ρ rows (List.replicate rows.length true) (by simp)
  rw [positiveZip] at h
  refine h.trans ?_
  constructor
  · rintro ⟨snap,live,bits⟩
    have len := snapshotLength f ρ rows snap live
    exact ⟨snap,live,(allTrueBits snap).mpr (by simpa only [len] using bits)⟩
  · rintro ⟨snap,live,yes⟩
    have len := snapshotLength f ρ rows snap live
    exact ⟨snap,live,by simpa only [len] using (allTrueBits snap).mp yes⟩

private theorem appendTape (f ρ : Nat → Nat) (pre tail : List BitRow) :
    ClauseHolds f ρ (pre ++ tail) ↔ ClauseHolds f ρ pre ∧ ClauseHolds f ρ tail :=
  ⟨fun all => ⟨fun r h => all r (List.mem_append_left _ h),fun r h => all r (List.mem_append_right _ h)⟩,
    fun h r used => (List.mem_append.mp used).elim (h.1 r) (h.2 r)⟩

theorem exactPositivePrefixAndBooleanSuffix : ExactPositivePrefixAndBooleanSuffix := by
  intro f ρ pre tail p positive
  constructor
  · rintro ⟨graphPass,snap,actual,accepts⟩
    let bits := snap.map Prod.snd
    have size : bits.length = tail.length := by
      simpa only [bits,List.length_map] using (snapshotLength f ρ tail snap actual)
    have member := (exactAcceptedVectors p positive tail.length bits).mpr ⟨size,accepts⟩
    refine ⟨_,List.mem_map.mpr ⟨bits,member,rfl⟩,?_⟩
    exact (appendTape f ρ _ _).mpr
      ⟨(positiveTape f ρ pre).mpr graphPass,(exactBitTape f ρ tail bits size).mpr ⟨snap,actual,rfl⟩⟩
  · rintro ⟨branch,used,all⟩
    obtain ⟨bits,member,rfl⟩ := List.mem_map.mp used
    obtain ⟨size,accepted⟩ := (exactAcceptedVectors p positive tail.length bits).mp member
    obtain ⟨graphPass,tailHolds⟩ := (appendTape f ρ _ _).mp all
    obtain ⟨snap,actual,eq⟩ := (exactBitTape f ρ tail bits size).mp tailHolds
    refine ⟨(positiveTape f ρ pre).mp graphPass,snap,actual,?_⟩
    change OriginalPlainTerminalMatrix.readBits p (snap.map Prod.snd) = some (positive,[])
    rwa [eq]

theorem exactPrintedNormalizedBoolClauses : ExactPrintedNormalizedBoolClauses := by
  intro f θ known gates p plain positive
  let gs := circuit known gates p
  have graph :
      OriginalPrintedCircuitNormalization.Holds f θ gs ↔
        ∃ snap : Snapshot, actualRows f θ (OriginalNormalizedCircuitMatrix.rowsList gs) snap ∧ AllTrue snap := by
    constructor
    · intro holds
      exact ⟨passingList θ gs,(exactPositiveCircuitSnapshots f θ gs _).mpr ⟨holds,rfl⟩⟩
    · rintro ⟨snap,actual,yes⟩
      exact ((exactPositiveCircuitSnapshots f θ gs snap).mp ⟨actual,yes⟩).1
  exact (and_congr graph (exactPlainTerminalSuffix f θ p plain positive)).trans
    (exactPositivePrefixAndBooleanSuffix f θ _ _ p positive)

end LogicLineages.PermittedControl.OriginalPrintedTerminalBitClauses
