module
public import LogicLineages.PermittedControl.OriginalPrintedRawClauseAssemblyTargets
import LogicLineages.PermittedControl.OriginalPrintedRawPositionalTerminalProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedRawClauseAssembly
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open HeterogeneousSignedMatrixSlice (Row encodeRow)
open ActualBitFamilyRawLayout (encodeBitRow encodeFamily)
open OriginalPrintedTerminalBitClauses (vectors accepted clauses zipBits)
open OriginalPrintedRawPositionalTerminal (finishCode exactOriginalRawPositionalFinish)

private theorem vectorLength (n : Nat) (bits : List Bool) : bits ∈ vectors n ↔ bits.length = n := by
  induction n generalizing bits with
  | zero => cases bits <;> simp [vectors]
  | succ n ih =>
    cases bits with
    | nil => simp [vectors]
    | cons b bs => cases b <;> simp [vectors,ih]

theorem exactOriginalRawAcceptedChoices : ExactOriginalRawAcceptedChoices := by
  refine ⟨?_,?_⟩
  · intro p polarity n
    unfold acceptedCode accepted
    apply List.filter_congr
    intro bits _
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact exactOriginalRawPositionalFinish p bits polarity
  · intro p bits
    simp only [acceptedCode,List.mem_filter,decide_eq_true_eq,vectorLength]

private theorem zipExact (rows : List Row) (bits : List Bool) :
    (rows.map encodeRow).zip bits = (zipBits rows bits).map encodeBitRow := by
  induction rows generalizing bits with
  | nil => cases bits <;> rfl
  | cons row rows ih =>
    cases bits with
    | nil => rfl
    | cons b tail =>
      change (encodeRow row,b) :: (rows.map encodeRow).zip tail =
        (encodeRow row,b) :: (zipBits rows tail).map encodeBitRow
      rw [ih]

theorem exactOriginalRawClauseAssembly : ExactOriginalRawClauseAssembly := by
  intro pre tail p polarity
  simp only [clausesCode,List.length_map,exactOriginalRawAcceptedChoices.1,encodeFamily,
    clauses,List.map_map,Function.comp_def,List.map_append,zipExact] <;> rfl

theorem exactOriginalRawClausePositions : ExactOriginalRawClausePositions := by
  intro p branch used
  obtain ⟨bits,accepted,eq⟩ := List.mem_map.mp used
  subst branch
  have sameLen := ((exactOriginalRawAcceptedChoices.2 (p.1,p.2.1,p.2.2.2.length) bits).mp accepted).1
  refine ⟨bits,accepted,?_⟩
  simp [List.take_append_length,List.drop_append_length,sameLen]

end LogicLineages.PermittedControl.OriginalPrintedRawClauseAssembly
