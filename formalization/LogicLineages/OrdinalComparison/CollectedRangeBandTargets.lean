module
public import LogicLineages.OrdinalComparison.CollectedRangeBandDefinitions
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def ActualOmegaHeadFormula : Prop :=
  ∀ n : Nat, actualProfileHead profileOmegaNote n=Phi (n+2)+1

def CollectedRangeThresholdCode : Prop :=
  Primrec encodedCollectedRangeThreshold ∧ ∀ A : CollectedPositiveNF,
    encodedCollectedRangeThreshold (collectedPositiveEncode A)=collectedRangeThreshold A

def CollectedNonlinearRangeBand : Prop :=
  ∀ (c b : Nat) (tags : CollectedPositiveTags), CollectedTagsValid tags → tags≠.nil →
    ∀ x : Nat, collectedRangeThreshold (.mk c b tags)≤x →
      let E := actualCollectedPositiveEval (.mk c b tags) x
      let Y := actualCollectedMaximumPeak tags x
      ∃ s : Nat, Y=Phi s ∧ Y<E ∧ E<Phi (s+1) ∧ E<actualProfileHead profileOmegaNote Y

end LogicLineages.OrdinalComparison.Targets
