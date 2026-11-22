module
public import LogicLineages.PermittedControl.OriginalPrintedNewCutoffPartitionTargets
import LogicLineages.PermittedControl.OriginalPrintedNewCutoffPartitionFundingProof
import LogicLineages.PermittedControl.OriginalPrintedNewCutoffLowProof
import LogicLineages.PermittedControl.OriginalPrintedRankedLiteralHighFundingProof
import LogicLineages.PermittedControl.OriginalPrintedRankedLiteralHighSourceProof
import LogicLineages.PermittedControl.OriginalRankedLiteralClauseHighPointProof
import LogicLineages.PermittedControl.ActualFiniteOrderBranchesCoverageProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedNewCutoffPartition
open ActualFiniteOrderBranches (Pattern actualPattern exactActualBranchCoverage guard realized)
open OriginalPrintedPlainMatrixOrderBranches (branches SourceAccepts)
open OriginalPrintedPlainMatrixLinearProjection (top)
open OriginalPrintedPlainMatrixInfiniteLow (matrix)
open OriginalMatrixDenseRanks (support)
open OriginalPrintedNewCutoffLow (exactPrintedNewCutoffLowAt)
open OriginalPrintedRankedLiteralHigh (cutoff PaidSupport rankedFamily exactOriginalChartFunding exactRankedOriginalBoolSource)
open OriginalRankedLiteralClauseHigh (highPackets exactRankedLiteralHigh)
open ActualBoundedSignedRoutes (PacketHolds)

theorem exactOriginalPrintedNewCutoffPartition : ExactOriginalPrintedNewCutoffPartition := by
  intro f B selected θ known gates p plain positive prior
  classical
  let names := support (matrix known gates p)
  let C := cutoff B known gates p positive
  have high (nonempty : names ≠ []) (paid : PaidSupport B θ known gates p positive)
      (branch : Pattern) (member : branch ∈ branches known gates p) (ordered : (guard branch).eval θ) :
      SourceAccepts f θ known gates p positive ↔
        ∃ q ∈ highPackets branch.1 (top branch) (rankedFamily known gates p positive branch),
          PacketHolds f (realized θ branch) (top branch) (realized θ branch (top branch)) q := by
    let z := realized θ branch (top branch)
    obtain ⟨_,minimum,same⟩ := exactActualGreatestPaysChart B θ known gates p positive nonempty paid branch member ordered
    have cl := exactRankedOriginalBoolSource f θ known gates p plain positive branch member ordered z
    rw [same] at cl
    have setup := exactOriginalChartFunding B θ known gates p positive paid branch member ordered
    exact cl.trans (exactRankedLiteralHigh f B selected branch.1 (top branch) (realized θ branch)
      (rankedFamily known gates p positive branch) setup.1 z (setup.2 z minimum).1)
  constructor
  · rintro ⟨outside,original⟩
    by_cases low : ∃ name ∈ names, θ name < C
    · obtain ⟨name,member,below⟩ := low
      exact Or.inl ⟨name,member,below,
        (exactPrintedNewCutoffLowAt f B θ known gates p plain positive prior name member below).mp ⟨outside,original⟩⟩
    · by_cases empty : names = []
      · exact Or.inr (Or.inr ⟨empty,outside,original⟩)
      · have funded : PaidSupport B θ known gates p positive :=
          fun name member => Nat.le_of_not_gt (fun below => low ⟨name,member,below⟩)
        let branch := actualPattern θ names
        obtain ⟨used,ordered⟩ := exactActualBranchCoverage θ names
        exact Or.inr (Or.inl ⟨empty,funded,outside,branch,used,ordered,
          (high empty funded branch used ordered).mp original⟩)
  · rintro (⟨name,member,below,low⟩ | ⟨nonempty,funded,outside,branch,used,ordered,actual⟩ | ⟨_,outside,truth⟩)
    · exact (exactPrintedNewCutoffLowAt f B θ known gates p plain positive prior name member below).mpr low
    · exact ⟨outside,(high nonempty funded branch used ordered).mpr actual⟩
    · exact ⟨outside,truth⟩

end LogicLineages.PermittedControl.OriginalPrintedNewCutoffPartition
