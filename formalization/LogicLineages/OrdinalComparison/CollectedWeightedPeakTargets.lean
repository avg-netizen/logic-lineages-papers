module
public import LogicLineages.OrdinalComparison.CollectedPeakDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def CollectedWeightedPeakBand : Prop :=
  ∀ tags : CollectedPositiveTags, CollectedTagsValid tags → tags≠.nil → ∀ x : Nat, 2≤x →
    let Y := actualCollectedMaximumPeak tags x
    let C := collectedCoefficientSum tags
    Y<actualCollectedTagsEval tags x ∧ actualCollectedTagsEval tags x<2*C*Y ∧
    ∃ s : Nat, Y=Phi s

end LogicLineages.OrdinalComparison.Targets
