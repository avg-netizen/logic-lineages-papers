module
public import LogicLineages.OrdinalComparison.CollectedFiniteClosureDefinitions
public import LogicLineages.OrdinalComparison.EncodedCollectedThresholdDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

def collectedRootCodeBound (forms : List CollectedPositiveNF) : Nat :=
  forms.foldr (fun A bound => max (collectedPositiveEncode A) bound) 0

def collectedFiniteZeroBound (forms : List CollectedPositiveNF) : Nat :=
  max (collectedFamilyThreshold forms) (max 4 (8*collectedRootCodeBound forms+1))

def encodedCollectedZeroBound (codes : List Nat) : Nat :=
  max (encodedCollectedFamilyThreshold codes) (max 4 (8*(codes.foldr max 0)+1))

end LogicLineages.OrdinalComparison
