module
public import LogicLineages.PermittedControl.OriginalPrintedRankedLiteralHighTargets
import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjectionTransportProof
import LogicLineages.PermittedControl.OriginalPrintedTerminalBitClausesProof
import LogicLineages.PermittedControl.OriginalNormalizedMatrixPositiveSnapshotsProof
import LogicLineages.PermittedControl.OriginalPlainTerminalMatrixProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedRankedLiteralHigh
open OriginalPrintedPlainMatrixInfiniteLow (circuit matrix)
open OriginalPrintedPlainMatrixLinearProjection (top replay transportPart)
open OriginalNormalizedCircuitMatrix (rowsList passingList)
open OriginalNormalizedMatrixPositiveSnapshots (AllTrue exactPositiveCircuitSnapshots)
open OriginalPlainTerminalMatrix (rows accepts exactPlainTerminalSuffix)
open OriginalPrintedTerminalBitClauses (exactPositivePrefixAndBooleanSuffix)
open HeterogeneousSignedMatrixSlice (Row Snapshot actualRows)
open ActualFiniteOrderBranches (rename realized)
open OriginalMatrixDenseRanks (renameRow)

theorem exactRankedOriginalBoolSource : ExactRankedOriginalBoolSource := by
  intro f θ known gates p plain positive branch member ordered z
  let gs := circuit known gates p
  let pre := rowsList gs
  let tail := rows p
  let later := Function.update (realized θ branch) (top branch) z
  let source := replay θ known gates p branch z
  let ren := renameRow (rename branch)
  have g (xs : Snapshot) : actualRows f later (pre.map ren) xs ↔ actualRows f source pre xs :=
    transportPart θ known gates p branch member ordered z pre
      (fun r h => List.mem_append_left _ h) f xs
  have t (xs : Snapshot) : actualRows f later (tail.map ren) xs ↔ actualRows f source tail xs :=
    transportPart θ known gates p branch member ordered z tail
      (fun r h => List.mem_append_right _ h) f xs
  have graph : OriginalPrintedCircuitNormalization.Holds f source gs ↔
      ∃ xs : Snapshot, actualRows f later (pre.map ren) xs ∧ AllTrue xs := by
    constructor
    · intro passed
      let xs := passingList source gs
      obtain ⟨atSource,yes⟩ := (exactPositiveCircuitSnapshots f source gs xs).mpr ⟨passed,rfl⟩
      exact ⟨xs,(g xs).mpr atSource,yes⟩
    · rintro ⟨xs,ranked,yes⟩
      exact ((exactPositiveCircuitSnapshots f source gs xs).mp ⟨(g xs).mp ranked,yes⟩).1
  have terminal :
      (∃ xs : Snapshot, actualRows f source tail xs ∧ accepts p positive xs) ↔
      ∃ xs : Snapshot, actualRows f later (tail.map ren) xs ∧ accepts p positive xs := by
    constructor
    · rintro ⟨xs,under,yes⟩
      exact ⟨xs,(t xs).mpr under,yes⟩
    · rintro ⟨xs,under,yes⟩
      exact ⟨xs,(t xs).mp under,yes⟩
  exact (and_congr graph ((exactPlainTerminalSuffix f source p plain positive).trans terminal)).trans
    (exactPositivePrefixAndBooleanSuffix f later (pre.map ren) (tail.map ren) p positive)

end LogicLineages.PermittedControl.OriginalPrintedRankedLiteralHigh
