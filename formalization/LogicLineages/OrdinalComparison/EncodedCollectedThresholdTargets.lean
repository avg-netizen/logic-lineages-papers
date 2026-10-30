module
public import LogicLineages.OrdinalComparison.EncodedCollectedThresholdDefinitions
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def EncodedCollectedThresholdDataPrimitiveRecursive : Prop := Primrec encodedCollectedThresholdData

def EncodedCollectedThresholdDataCorrect : Prop :=
  ∀ tags : CollectedPositiveTags,
    encodedCollectedThresholdData (collectedTagsEncode tags)=
      (collectedCoefficientSum tags,collectedTagsOneInputThreshold tags)

def EncodedCollectedThresholdPrimitiveRecursive : Prop :=
  Primrec encodedCollectedThreshold ∧ Primrec encodedCollectedFamilyThreshold

def EncodedCollectedThresholdCorrect : Prop :=
  ∀ A : CollectedPositiveNF,
    encodedCollectedThreshold (collectedPositiveEncode A)=collectedOneInputThreshold A

def EncodedCollectedFamilyThresholdCorrect : Prop :=
  ∀ forms : List CollectedPositiveNF,
    encodedCollectedFamilyThreshold (forms.map collectedPositiveEncode)=collectedFamilyThreshold forms

end LogicLineages.OrdinalComparison.Targets
