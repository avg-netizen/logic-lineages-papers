module
public import LogicLineages.PermittedControl.ActualBitFamilyLowSlicesTargets
import LogicLineages.PermittedControl.ActualGuardedResidualBitFamilyProof
import LogicLineages.PermittedControl.OriginalPrintedTerminalBitClausesBitsProof
import LogicLineages.PermittedControl.HeterogeneousSignedMatrixSliceRowsProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBitFamilyLowSlices
open OriginalPrintedTerminalBitClauses (BitRow ClauseHolds zipBits exactBitTape)
open ActualGuardedResidualBitFamily (exactZipRows)
open HeterogeneousSignedMatrixSlice (Row RowResult HitRows sliceRows exactMatrixSnapshots)

theorem exactOrderedHitExtraction : ExactOrderedHitExtraction := by
  intro statuses
  induction statuses with
  | nil =>
    intro rs
    constructor
    · intro eq
      have same : [] = rs := Option.some.inj eq
      subst rs
      exact .nil
    · intro hit
      cases hit
      rfl
  | cons cell more ih =>
    rcases cell with ⟨test,status⟩
    intro rs
    cases status with
    | none =>
      constructor
      · intro eq
        cases eq
      · intro hit
        cases hit
    | some payload =>
      cases payload with
      | none =>
        constructor
        · intro eq
          cases eq
        · intro hit
          cases hit
      | some pair =>
        rcases pair with ⟨b,terms⟩
        constructor
        · intro live
          cases h : extractHits more with
          | none =>
            have impossible : (none : Option (List Row)) = some rs := by simpa [extractHits,h] using live
            cases impossible
          | some out =>
            have eq : (test,b,terms)::out = rs := Option.some.inj (by simpa [extractHits,h] using live)
            subst rs
            exact .cons ((ih out).mp h)
        · intro live
          cases live with
          | @cons _ _ _ _ tail actual =>
            simp [extractHits,(ih tail).mpr actual]

theorem hitLength (statuses : List RowResult) (rs : List Row) (hit : HitRows statuses rs) :
    rs.length = statuses.length := by
  induction hit with
  | nil => rfl
  | cons _ ih => exact congrArg Nat.succ ih

theorem rowsLength (f : Nat → Nat) (name a : Nat) (clause : List BitRow) (rs : List Row)
    (hit : HitRows (sliceRows f name a (originalRows clause)) rs) : (wantedBits clause).length = rs.length := by
  have h := hitLength _ _ hit
  simpa only [sliceRows,originalRows,wantedBits,List.length_map] using h.symm

private theorem zipIdentity (c : List BitRow) : zipBits (originalRows c) (wantedBits c) = c := by
  induction c with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨row,bit⟩
    exact congrArg (List.cons (row,bit)) ih

theorem exactBitClauseSlice : ExactBitClauseSlice := by
  intro f ρ name a clause atRaw
  let rs := originalRows clause
  let bits := wantedBits clause
  let tape := (exactBitTape f ρ rs bits (by simp [rs,bits,originalRows,wantedBits]))
  have static : zipBits rs bits = clause := zipIdentity clause
  constructor
  · intro holds
    rw [← static] at holds
    obtain ⟨snap,actual,signs⟩ := tape.mp holds
    obtain ⟨out,hit,measured⟩ := (exactMatrixSnapshots f ρ name a rs atRaw snap).mp actual
    let child := zipBits out bits
    refine ⟨child,?_,(exactBitTape f ρ out bits (rowsLength f name a clause out hit)).mpr ⟨snap,measured,signs⟩⟩
    change (extractHits (sliceRows f name a rs)).map _ = _
    rw [(exactOrderedHitExtraction _ _).mpr hit] <;> rfl
  · rintro ⟨child,defined,holds⟩
    cases h : extractHits (sliceRows f name a rs) with
    | none =>
      have impossible : (none : Option (List BitRow)) = some child := by
        simpa only [sliceClause,rs,h,Option.map_none] using defined
      cases impossible
    | some out =>
      have exactChildren : zipBits out bits = child := Option.some.inj (by
        simpa only [sliceClause,rs,bits,h,Option.map_some] using defined)
      have hit := (exactOrderedHitExtraction _ _).mp h
      rw [← exactChildren] at holds
      obtain ⟨snap,measured,signs⟩ := (exactBitTape f ρ out bits (rowsLength f name a clause out hit)).mp holds
      rw [← static]
      exact tape.mpr ⟨snap,(exactMatrixSnapshots f ρ name a rs atRaw snap).mpr ⟨out,hit,measured⟩,signs⟩

end LogicLineages.PermittedControl.ActualBitFamilyLowSlices
