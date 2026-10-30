module
public import LogicLineages.OrdinalComparison.EncodedCollectedMergeDefinitions
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def EncodedCollectedInsertPrimitiveRecursive : Prop :=
  Primrec (fun p : (Nat × Nat) × Nat => encodedCollectedInsert p.1.1 p.1.2 p.2)

def EncodedCollectedMergePrimitiveRecursive : Prop := Primrec₂ encodedCollectedMerge

def EncodedCollectedAddPrimitiveRecursive : Prop := Primrec₂ encodedCollectedAdd

def EncodedCollectedInsertCorrect : Prop :=
  ∀ (rho : NONote) (A : CollectedPositiveNF) (a : Nat) (tags : CollectedPositiveTags),
    encodedCollectedInsert (collectedTagKey rho A) a (collectedTagsEncode tags)=
      collectedTagsEncode (collectedTagInsert rho A a tags)

def EncodedCollectedMergeCorrect : Prop :=
  ∀ (left right : CollectedPositiveTags),
    encodedCollectedMerge (collectedTagsEncode left) (collectedTagsEncode right)=
      collectedTagsEncode (collectedTagsMerge left right)

def EncodedCollectedAddCorrect : Prop :=
  ∀ (A B : CollectedPositiveNF),
    encodedCollectedAdd (collectedPositiveEncode A) (collectedPositiveEncode B)=
      collectedPositiveEncode (collectedPositiveAdd A B)

end LogicLineages.OrdinalComparison.Targets
