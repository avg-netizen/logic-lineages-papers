module
public import LogicLineages.PermittedControl.ActualBitFamilyExistentialLowTargets
import LogicLineages.PermittedControl.ActualBitFamilyExistentialLowLocalityProof
import LogicLineages.PermittedControl.OriginalPrintedZeroSupportSnapshotProof
import LogicLineages.PermittedControl.OriginalPrintedTerminalBitClausesBitsProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBitFamilyExistentialLow
open ActualGuardedResidualBitFamily (Family Holds)
open ActualBitFamilyLowSlices (coordinates originalRows wantedBits)
open OriginalPrintedTerminalBitClauses (BitRow ClauseHolds zipBits exactBitTape)
open OriginalPrintedZeroSupport (closedSnapshot exactClosedActualSnapshot)
open HeterogeneousSignedMatrixSlice (Row)

private theorem recreate (clause : List BitRow) : zipBits (originalRows clause) (wantedBits clause) = clause := by
  induction clause with
  | nil => rfl
  | cons r rs ih =>
    rcases r with ⟨row,b⟩
    exact congrArg (List.cons (row,b)) ih

private theorem closedTruth (f ρ : Nat → Nat) (clause : List BitRow)
    (empty : ∀ row ∈ originalRows clause, row.2.2 = []) :
    closedClause clause = true ↔ ClauseHolds f ρ clause := by
  let rs := originalRows clause
  let bits := wantedBits clause
  have tape := exactBitTape f ρ rs bits (by simp [rs,bits,originalRows,wantedBits])
  rw [show zipBits rs bits = clause from recreate clause] at tape
  have eq :
      (∃ snap, closedSnapshot rs = some snap ∧ snap.map Prod.snd = bits) ↔ ClauseHolds f ρ clause := by
    refine Iff.trans ?_ tape.symm
    constructor
    · rintro ⟨snap,code,h⟩
      exact ⟨snap,((exactClosedActualSnapshot f ρ rs snap).mp code).2,h⟩
    · rintro ⟨snap,rows,h⟩
      exact ⟨snap,(exactClosedActualSnapshot f ρ rs snap).mpr ⟨empty,rows⟩,h⟩
  refine Iff.trans ?_ eq
  change (match closedSnapshot rs with
    | none => false
    | some vals => decide (vals.map Prod.snd = bits)) = true ↔ _
  cases coded : closedSnapshot rs <;> simp [coded]

theorem exactBitFamilyClosed : ExactBitFamilyClosed := by
  intro f family empty
  have noRank : coordinates family = ∅ := Finset.card_eq_zero.mp empty
  have hasNoTerms (clause : List BitRow) (member : clause ∈ family) :
      ∀ row ∈ originalRows clause, row.2.2 = [] := by
    intro row used
    obtain ⟨r,old,rfl⟩ := List.mem_map.mp used
    cases shape : r.1.2.2 with
    | nil => rfl
    | cons t ts =>
      have term : t ∈ r.1.2.2 := by rw [shape]; exact List.mem_cons_self
      have wrong := exactClauseOperandInUnion family clause member r old t term
      rw [noRank] at wrong
      exact False.elim (Finset.notMem_empty _ wrong)
  constructor
  · intro yes
    obtain ⟨clause,used,answer⟩ := List.any_eq_true.mp yes
    exact ⟨fun _ => 0,clause,used,(closedTruth f (fun _ => 0) clause (hasNoTerms clause used)).mp answer⟩
  · rintro ⟨ρ,clause,used,live⟩
    exact List.any_eq_true.mpr ⟨clause,used,(closedTruth f ρ clause (hasNoTerms clause used)).mpr live⟩

end LogicLineages.PermittedControl.ActualBitFamilyExistentialLow
