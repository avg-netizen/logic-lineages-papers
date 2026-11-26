module
public import LogicLineages.PermittedControl.OriginalPrintedUniformHighResidualTargets
import LogicLineages.PermittedControl.OriginalPrintedUniformHighResidualTransportProof
import LogicLineages.PermittedControl.OriginalPrintedRankedLiteralHighProjectionProof
import LogicLineages.PermittedControl.OriginalPrintedHighResidualChartProof
import LogicLineages.PermittedControl.ActualGreatestRouteResidualProof
import LogicLineages.PermittedControl.ActualLowerRankChartRowsProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedUniformHighResidual
open OriginalPrintedHighResidual (guardedRows GuardedAccepts exactOriginalDenseLowerChart)
open OriginalPrintedRankedLiteralHigh (cutoff exactOriginalPrintedRankedHighProjection)
open OriginalPrintedPlainMatrixLinearProjection (top)
open OriginalPrintedPlainMatrixOrderBranches (renamed)
open ActualFiniteOrderBranches (realized)
open ActualLowerRankChartRows (lowerChart exactLowerRankChartRows)
open ActualGreatestRouteResidual (Residual LowerMatrix rows exactActualLowerRouteFamily)
open OriginalMatrixLowDimension (supportSet dimension)

private theorem combinedScope (f ρ : Nat → Nat) (C top : Nat) (out : Residual)
    (scope : ∀ rank ∈ supportSet (rows out), rank < top) :
    ∀ rank ∈ supportSet (guardedRows C top out), rank < top := by
  intro rank used
  obtain ⟨row,member,terms⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp used)
  rcases List.mem_append.mp member with pre | tail
  · obtain ⟨g,hg,eq⟩ := List.mem_map.mp pre
    subst row
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp terms
    exact ((exactLowerRankChartRows f ρ C top).2 g hg).2 t ht
  · exact scope rank (List.mem_toFinset.mpr (List.mem_flatMap.mpr ⟨row,tail,terms⟩))

theorem exactOriginalPrintedUniformHighResidual : ExactOriginalPrintedUniformHighResidual := by
  intro f B selected θ known gates p plain positive paid branch member ordered nonempty prior C minimum rs stable
  let ρ := realized θ branch
  let greatest := top branch
  have original := exactOriginalDenseLowerChart B θ known gates p positive branch member ordered nonempty
  have chart := (exactLowerRankChartRows f ρ C greatest).1.mpr (original.2 paid)
  have below := (exactActualLowerRouteFamily f ρ greatest C (candidates known gates p positive branch)
    (candidateShape known gates p positive branch)).1
  refine ⟨?_,?_⟩
  · intro out used
    have scope := combinedScope f ρ C greatest out (below out used)
    have included : supportSet (guardedRows C greatest out) ⊆
        (supportSet (renamed known gates p branch)).erase greatest := by
      intro rank atRank
      have less := scope rank atRank
      exact Finset.mem_erase.mpr ⟨ne_of_lt less,original.1 rank less.le⟩
    exact ⟨included,(Finset.card_le_card included).trans_lt
      (Finset.card_erase_lt_of_mem (original.1 greatest le_rfl))⟩
  · have separate :
        (∃ out ∈ rs, GuardedAccepts f ρ C greatest out) ↔ ∃ out ∈ rs, LowerMatrix f ρ out := by
      constructor
      · rintro ⟨out,used,_,passes⟩
        exact ⟨out,used,passes⟩
      · rintro ⟨out,used,passes⟩
        exact ⟨out,used,chart,passes⟩
    have transport := exactUniformHighProjectionTransport f θ B known gates p positive branch
    exact (and_congr Iff.rfl (separate.trans transport)).trans
      (exactOriginalPrintedRankedHighProjection f B selected θ known gates p plain positive paid branch member
        ordered nonempty prior stable)

end LogicLineages.PermittedControl.OriginalPrintedUniformHighResidual
