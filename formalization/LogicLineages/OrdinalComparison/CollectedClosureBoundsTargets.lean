module
public import LogicLineages.OrdinalComparison.CollectedClosureBoundsDefinitions
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def CollectedCoefficientCodeBound : Prop :=
  ∀ tags : CollectedPositiveTags, collectedCoefficientSum tags≤collectedTagsEncode tags

def CollectedComponentCodeBounds : Prop :=
  ∀ (c b : Nat) (tags : CollectedPositiveTags),
    c≤collectedPositiveEncode (.mk c b tags) ∧ b≤collectedPositiveEncode (.mk c b tags) ∧
    collectedCoefficientSum tags≤collectedPositiveEncode (.mk c b tags)

def CollectedClosureBounds : Prop :=
  ∀ forms : List CollectedPositiveNF, ∀ A∈collectedFiniteClosure forms,
    collectedPositiveEncode A≤collectedRootCodeBound forms ∧
    collectedOneInputThreshold A≤collectedFamilyThreshold forms

def EncodedCollectedZeroBoundPrimitiveRecursive : Prop := Primrec encodedCollectedZeroBound

def EncodedCollectedZeroBoundCorrect : Prop :=
  ∀ forms : List CollectedPositiveNF,
    encodedCollectedZeroBound (forms.map collectedPositiveEncode)=collectedFiniteZeroBound forms

end LogicLineages.OrdinalComparison.Targets
