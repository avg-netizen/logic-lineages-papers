module
public import LogicLineages.PermittedControl.OriginalProjectedMatrixSemanticsTargets
import LogicLineages.PermittedControl.PreparedParameterActualProof
import LogicLineages.PermittedControl.OriginalNormalizedMatrixPositiveSnapshotsShapeProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalProjectedMatrixSemantics
open PreparedProjection (LowerOperand lowerOperandRead preparedTiedProjection)
open HeterogeneousSignedMatrixSlice (Row Snapshot actualRows)
open OriginalNormalizedMatrixPositiveSnapshots (AllTrue allAppend)
open OriginalMatrixLinearLowerTable (Live)
open SignedRowSliceValue (valueAt)

private theorem one (f ρ : Nat → Nat) (op : LowerOperand) (value : Int) :
    valueAt f ρ 0 (availableRow op).2.2 value ↔
      ∃ v : Nat, lowerOperandRead f ρ op = some (some v) ∧ value = (v : Int) := by
  constructor
  · rintro ⟨values,live,eq⟩
    cases values with
    | nil => exact False.elim live
    | cons v rest =>
        cases rest with
        | cons w rest => exact False.elim live.2.2
        | nil =>
            have h : (v : Int) = value := by
              simpa [availableRow,MixedSameRankResidue.actualSum] using eq
            exact ⟨v,live.2.1,h.symm⟩
  · rintro ⟨v,hit,rfl⟩
    exact ⟨[v],⟨(preparedTiedProjection.1 f ρ op v).mp hit,hit,True.intro⟩,
      by simp [availableRow,MixedSameRankResidue.actualSum]⟩

theorem actualLength (f ρ : Nat → Nat) (rows : List Row) (snap : Snapshot)
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

private theorem all (f ρ : Nat → Nat) (ops : List LowerOperand) :
    Live f ρ ops ↔ ∃ guards : Snapshot, actualRows f ρ (availabilityRows ops) guards ∧ AllTrue guards := by
  induction ops with
  | nil =>
      constructor
      · intro _
        exact ⟨[],True.intro,by simp [AllTrue]⟩
      · intro _ op used
        cases used
  | cons op ops ih =>
      constructor
      · intro live
        obtain ⟨v,hit⟩ := live op List.mem_cons_self
        obtain ⟨rest,liveRest,yes⟩ := ih.mp (fun u hu => live u (List.mem_cons_of_mem _ hu))
        have head := (one f ρ op (v : Int)).mpr ⟨v,hit,rfl⟩
        refine ⟨(v,true)::rest,⟨True.intro,head,(show (0 : Int) ≤ (v : Int) by omega),liveRest⟩,?_⟩
        exact (allAppend [(v,true)] rest).mpr ⟨by simp [AllTrue],yes⟩
      · rintro ⟨guards,live,yes⟩ u used
        cases guards with
        | nil => exact False.elim live
        | cons head rest =>
            rcases List.mem_cons.mp used with eq | tail
            · subst u
              obtain ⟨v,hit,_⟩ := (one f ρ op head.1).mp live.2.1
              exact ⟨v,hit⟩
            · exact ih.mpr ⟨rest,live.2.2.2,fun x member => yes x (List.mem_cons_of_mem _ member)⟩ u tail

theorem exactAvailabilityRows : ExactAvailabilityRows := by
  refine ⟨one,all,?_⟩
  intro f ρ ops op used failed positive
  have live : Live f ρ ops := (all f ρ ops).mpr positive
  obtain ⟨v,hit⟩ := live op used
  rcases failed with invalid | miss
  · rw [invalid] at hit
    cases hit
  · rw [miss] at hit
    cases hit

end LogicLineages.PermittedControl.OriginalProjectedMatrixSemantics
