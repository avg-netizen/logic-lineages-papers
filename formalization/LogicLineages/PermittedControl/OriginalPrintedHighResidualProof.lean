module
public import LogicLineages.PermittedControl.OriginalPrintedHighResidualTargets
import LogicLineages.PermittedControl.OriginalPrintedRankedLiteralHighProjectionProof
import LogicLineages.PermittedControl.OriginalRankedLiteralClauseHighPointProof
import LogicLineages.PermittedControl.ActualGreatestRouteResidualProof
import LogicLineages.PermittedControl.ActualLowerRankChartRowsProof
import LogicLineages.PermittedControl.OriginalPrintedHighResidualChartProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedHighResidual
open ActualLowerRankChartRows (lowerChart exactLowerRankChartRows)
open ActualGreatestRouteResidual (Residual LowerMatrix rows exactActualLowerRouteFamily)
open OriginalPrintedRankedLiteralHigh (cutoff chartMinimum rankedFamily exactOriginalPrintedRankedHighProjection)
open OriginalRankedLiteralClauseHigh (highPackets highPacketShape)
open OriginalPrintedPlainMatrixLinearProjection (top)
open OriginalPrintedPlainMatrixOrderBranches (renamed)
open OriginalMatrixLowDimension (supportSet dimension)
open ActualFiniteOrderBranches (realized)

private theorem guardedLower (f ρ : Nat → Nat) (C greatest : Nat) (out : Residual)
    (pure : ∀ rank ∈ supportSet (rows out), rank < greatest) :
    ∀ rank ∈ supportSet (guardedRows C greatest out), rank < greatest := by
  intro rank used
  obtain ⟨row,found,origin⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp used)
  rcases List.mem_append.mp found with pre | core
  · obtain ⟨g,hg,e⟩ := List.mem_map.mp pre
    subst row
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp origin
    exact ((exactLowerRankChartRows f ρ C greatest).2 g hg).2 t ht
  · exact pure rank (List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨row,core,origin⟩))

theorem exactOriginalPrintedHighResidual : ExactOriginalPrintedHighResidual := by
  intro f B selected θ known gates p plain positive paid branch member ordered nonempty prior C minimum rs stable
  let ρ := realized θ branch
  let greatest := top branch
  let family := rankedFamily known gates p positive branch
  let qs := highPackets branch.1 greatest family
  have decode := exactActualLowerRouteFamily f ρ greatest minimum qs
    (highPacketShape branch.1 greatest family)
  have dense := exactOriginalDenseLowerChart B θ known gates p positive branch member ordered nonempty
  have chart := (exactLowerRankChartRows f ρ C greatest).1.mpr (dense.2 paid)
  refine ⟨?_,?_⟩
  · intro out used
    have below := guardedLower f ρ C greatest out (decode.1 out used)
    have included : supportSet (guardedRows C greatest out) ⊆
        (supportSet (renamed known gates p branch)).erase greatest := by
      intro rank rk
      have lowered := below rank rk
      exact Finset.mem_erase.mpr ⟨ne_of_lt lowered,dense.1 rank lowered.le⟩
    exact ⟨included,(Finset.card_le_card included).trans_lt
      (Finset.card_erase_lt_of_mem (dense.1 greatest le_rfl))⟩
  · have join :
        (∃ out ∈ rs, GuardedAccepts f ρ C greatest out) ↔ ∃ out ∈ rs, LowerMatrix f ρ out := by
      constructor
      · rintro ⟨out,used,_,live⟩
        exact ⟨out,used,live⟩
      · rintro ⟨out,used,live⟩
        exact ⟨out,used,chart,live⟩
    exact (and_congr Iff.rfl (join.trans decode.2.symm)).trans
      (exactOriginalPrintedRankedHighProjection f B selected θ known gates p plain positive paid branch member
        ordered nonempty prior stable)

end LogicLineages.PermittedControl.OriginalPrintedHighResidual
