module
public import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjectionTargets
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesRealizationProof
import LogicLineages.PermittedControl.OriginalMatrixDenseRanksProof
import LogicLineages.PermittedControl.OriginalNormalizedCircuitMatrixProof
import LogicLineages.PermittedControl.OriginalPlainTerminalMatrixProof
import LogicLineages.PermittedControl.AffineCollapsePairListLowPrefixProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedCircuitSequential (Gate)
open ActualFiniteOrderBranches (Pattern guard rename realized exactBranchRealization)
open OriginalPrintedPlainMatrixOrderBranches (SourceAccepts branches renamed)
open OriginalPrintedPlainMatrixInfiniteLow (circuit matrix)
open OriginalMatrixDenseRanks (support renameRow exactRenamedMatrix)
open OriginalNormalizedCircuitMatrix (rowsList passingList exactNormalizedCircuitRows)
open OriginalPlainTerminalMatrix (rows accepts exactPlainTerminalSuffix)
open HeterogeneousSignedMatrixSlice (Row Snapshot actualRows)

theorem updatedTies (θ : Nat → Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula)
    (branch : Pattern) (member : branch ∈ branches known gates p)
    (ordered : (guard branch).eval θ) (z : Nat) :
    ∀ name ∈ support (matrix known gates p),
      Function.update (realized θ branch) (top branch) z (rename branch name) =
        replay θ known gates p branch z name := by
  have ties := (exactBranchRealization θ (support (matrix known gates p)) branch member ordered).2.2
  intro name used
  by_cases eq : rename branch name = top branch
  · simp [replay,used,eq]
  · simp [replay,used,eq,Function.update_of_ne eq,(ties name used).2]

theorem rowInRenamed (known : List Nat) (gates : List Gate) (p : NormalForm.Formula)
    (branch : Pattern) (row : Row) (member : row ∈ matrix known gates p) :
    renameRow (rename branch) row ∈ renamed known gates p branch :=
  List.mem_map.mpr ⟨row,member,rfl⟩

theorem transportPart (θ : Nat → Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula)
    (branch : Pattern) (member : branch ∈ branches known gates p)
    (ordered : (guard branch).eval θ) (z : Nat) (rs : List Row)
    (part : ∀ row ∈ rs, row ∈ matrix known gates p) (f : Nat → Nat) (snap : Snapshot) :
    actualRows f (Function.update (realized θ branch) (top branch) z)
      (rs.map (renameRow (rename branch))) snap ↔
      actualRows f (replay θ known gates p branch z) rs snap := by
  apply exactRenamedMatrix
  intro name hn
  obtain ⟨r,hr,inRow⟩ := List.mem_flatMap.mp hn
  exact updatedTies θ known gates p branch member ordered z name
    (List.mem_flatMap.mpr ⟨r,part r hr,inRow⟩)

theorem sourceActual (f θ : Nat → Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula)
    (plain : PreparedProjection.PlainPreparedFormula p) (positive : Bool)
    (source : SourceAccepts f θ known gates p positive) :
    ∃ snap : Snapshot, actualRows f θ (matrix known gates p) snap := by
  let gs := circuit known gates p
  obtain ⟨test,live,_⟩ := (exactPlainTerminalSuffix f θ p plain positive).mp source.2
  have core := exactNormalizedCircuitRows f θ gs
  exact ⟨passingList θ gs ++ test,
    (AffineCollapsePairListLow.actualRowsAppend f θ (rowsList gs) (rows p)
      (passingList θ gs) test core.1).mpr ⟨core.2.mpr source.1,live⟩⟩

end LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjection
