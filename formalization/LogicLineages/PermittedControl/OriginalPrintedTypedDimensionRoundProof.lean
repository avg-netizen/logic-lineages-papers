module
public import LogicLineages.PermittedControl.OriginalPrintedTypedDimensionRoundTargets
import LogicLineages.PermittedControl.OriginalPrintedNewCutoffLowProof
import LogicLineages.PermittedControl.OriginalMatrixLowDimensionProof
import LogicLineages.PermittedControl.OriginalPrintedHighResidualProof
import LogicLineages.PermittedControl.OriginalPrintedZeroSupportProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedTypedDimensionRound
open OriginalPrintedNewCutoffLow (exactPrintedNewCutoffLowStrips)
open OriginalPrintedHighResidual (exactOriginalPrintedHighResidual)
open OriginalPrintedZeroSupport (exactOriginalZeroSupport)
open OriginalMatrixLowDimension (exactLowFamilyDimension)
open OriginalPrintedRankedLiteralHigh (cutoff)
open OriginalPrintedPlainMatrixInfiniteLow (matrix)

theorem exactOriginalPrintedTypedDimensionRound : ExactOriginalPrintedTypedDimensionRound := by
  intro f B selected known gates p plain positive prior query ready next
  cases query with
  | closed θ =>
    exact ⟨True.intro,and_congr Iff.rfl
      (exactOriginalZeroSupport f θ known gates p plain ready positive).symm⟩
  | low ρ name =>
    exact ⟨exactLowFamilyDimension f name (cutoff B known gates p positive) (matrix known gates p) ready,
      exactPrintedNewCutoffLowStrips f B ρ known gates p plain positive prior name ready⟩
  | high θ chart =>
    obtain ⟨paid,member,ordered,nonempty,stable⟩ := ready
    have branch := exactOriginalPrintedHighResidual f B selected θ known gates p plain positive paid
      chart member ordered nonempty prior stable
    exact ⟨branch.1,branch.2.symm⟩

end LogicLineages.PermittedControl.OriginalPrintedTypedDimensionRound
