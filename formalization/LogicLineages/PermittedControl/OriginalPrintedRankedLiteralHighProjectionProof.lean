module
public import LogicLineages.PermittedControl.OriginalPrintedRankedLiteralHighTargets
import LogicLineages.PermittedControl.OriginalPrintedRankedLiteralHighFundingProof
import LogicLineages.PermittedControl.OriginalPrintedRankedLiteralHighSourceProof
import LogicLineages.PermittedControl.OriginalRankedLiteralClauseHighPointProof
import LogicLineages.PermittedControl.ActualSelectedSignedRouteProjectionChosenProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedRankedLiteralHigh
open OriginalPrintedPlainMatrixLinearProjection (top replay)
open OriginalPrintedPlainMatrixOrderBranches (SourceAccepts)
open ActualFiniteOrderBranches (realized)
open ActualBoundedSignedRoutes (PacketHolds)
open OriginalRankedLiteralClauseHigh (highPackets exactRankedLiteralHigh highPacketShape)
open ActualSelectedSignedRouteProjection (exactChosenRouteProjection)

theorem exactOriginalPrintedRankedHighProjection : ExactOriginalPrintedRankedHighProjection := by
  intro f B selected θ known gates p plain positive paid branch member ordered _ prior minimum family stable
  let base := realized θ branch
  let greatest := top branch
  have funded := exactOriginalChartFunding B θ known gates p positive paid branch member ordered
  have point (z : Nat) (high : minimum ≤ z) :
      SourceAccepts f (replay θ known gates p branch z) known gates p positive ↔
        ∃ q ∈ highPackets branch.1 greatest family, PacketHolds f base greatest z q := by
    have original := exactRankedOriginalBoolSource f θ known gates p plain positive branch member ordered z
    have highRow := exactRankedLiteralHigh f B selected branch.1 greatest base family funded.1 z
      (funded.2 z high).1
    exact original.trans highRow
  constructor
  · rintro ⟨outside,q,used,projected⟩
    obtain ⟨z,high,holds⟩ := (exactChosenRouteProjection f base greatest minimum q
      (highPacketShape branch.1 greatest family q used)).2.2.2.mp projected
    exact ⟨z,high,(stable z high).mpr outside,(point z high).mpr ⟨q,used,holds⟩⟩
  · rintro ⟨z,high,outside,src⟩
    obtain ⟨q,used,holds⟩ := (point z high).mp src
    exact ⟨(stable z high).mp outside,q,used,
      (exactChosenRouteProjection f base greatest minimum q
        (highPacketShape branch.1 greatest family q used)).2.2.2.mpr ⟨z,high,holds⟩⟩

end LogicLineages.PermittedControl.OriginalPrintedRankedLiteralHigh
