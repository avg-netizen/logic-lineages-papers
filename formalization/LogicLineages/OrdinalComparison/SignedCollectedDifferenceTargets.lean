module
public import LogicLineages.OrdinalComparison.SignedCollectedDifferenceDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def SignedCollectedDifferenceValue : Prop :=
  ∀ left right : CollectedPositiveTags, ∀ x : Nat,
    actualSignedCollectedValue (signedCollectedDifference left right) x=
      (actualCollectedTagsEval left x : Int)-(actualCollectedTagsEval right x : Int)

def SignedCollectedDifferenceValid : Prop :=
  ∀ left right : CollectedPositiveTags, CollectedTagsValid left → CollectedTagsValid right →
    SignedCollectedValid (signedCollectedDifference left right) ∧
    ∀ entry∈signedCollectedDifference left right,
      entry.1∈collectedDirectTags left ∨ entry.1∈collectedDirectTags right

def SignedCollectedDifferenceEmpty : Prop :=
  ∀ left right : CollectedPositiveTags, signedCollectedDifference left right=[] ↔ left=right

def SignedCollectedNFRowValue : Prop :=
  ∀ A B : CollectedPositiveNF, ∀ x : Nat,
    let row := signedCollectedNFRow A B
    row.1 + row.2.1*(x : Int) + actualSignedCollectedValue row.2.2 x =
      (actualCollectedPositiveEval A x : Int)-(actualCollectedPositiveEval B x : Int)

end LogicLineages.OrdinalComparison.Targets
