module
public import LogicLineages.PermittedControl.ActualNamedBitFamilyHighAboveTargets
import LogicLineages.PermittedControl.ActualNamedBitFamilyHighSetupProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualNamedBitFamilyHighAbove
open ActualNamedBitFamilyHigh (cutoff exactNamedHighSetup)
open ActualLowerRankChartRows (LowerChartCondition)
open ActualRankChartPrototype (seed)
open OriginalPrintedPlainMatrixLinearProjection (top)

theorem exactAboveHighSetup : ExactAboveHighSetup := by
  intro B C family names large p supports valid lower ready
  have smaller : LowerChartCondition (cutoff B family names) (top p) lower :=
    ⟨fun i below => large.trans (ready.1 i below),ready.2⟩
  have original := exactNamedHighSetup B family names p supports valid lower smaller
  refine ⟨original.1,?_⟩
  intro z paid
  have seedBound : seed (cutoff B family names) p lower ≤ z :=
    max_le (large.trans ((le_max_left _ _).trans paid)) ((le_max_right _ _).trans paid)
  exact original.2 z seedBound

end LogicLineages.PermittedControl.ActualNamedBitFamilyHighAbove
