module
public import LogicLineages.PermittedControl.OriginalPrintedGreatestResolvedProjectionTargets
import LogicLineages.PermittedControl.OriginalPrintedGreatestResolvedMatrixRankProof
import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjectionTransportProof
import LogicLineages.PermittedControl.OriginalMatrixDenseRanksProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedGreatestResolvedProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedCircuitSequential (Gate)
open OriginalPrintedGreatestResolvedMatrix (fullRows exactResolvedMatrixTopLinear)
open OriginalPrintedPlainMatrixOrderBranches (branches)
open OriginalPrintedPlainMatrixLinearProjection (top replay updatedTies)
open OriginalMatrixDenseRanks (support renameRow exactRenamedMatrix)
open ActualFiniteOrderBranches (Pattern rename guard realized)
open HeterogeneousSignedMatrixSlice (Row Snapshot actualRows)

/-- Transport transformed rows via their literal support, not via
identifying them with rows of the original graph. -/
theorem transport (θ : Nat → Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula)
    (branch : Pattern) (member : branch ∈ branches known gates p)
    (ordered : (guard branch).eval θ) (z : Nat) (rs : List Row)
    (part : ∀ row ∈ rs, row ∈ fullRows known gates p branch) (f : Nat → Nat) (snap : Snapshot) :
    actualRows f (Function.update (realized θ branch) (top branch) z)
      (rs.map (renameRow (rename branch))) snap ↔
      actualRows f (replay θ known gates p branch z) rs snap := by
  have subset := (exactResolvedMatrixTopLinear θ known gates p branch member ordered).1
  apply exactRenamedMatrix
  intro name hn
  obtain ⟨r,hr,inRow⟩ := List.mem_flatMap.mp hn
  exact updatedTies θ known gates p branch member ordered z name
    (subset name (List.mem_flatMap.mpr ⟨r,part r hr,inRow⟩))

end LogicLineages.PermittedControl.OriginalPrintedGreatestResolvedProjection
