module

public import LogicLineages.ComputabilityKnowledge.PredictionCanonicalListDefinitions

@[expose] public section
/-! Literal earlier-retained comparison clause of paper14 lem:list's scan.
The theorem, not a correctness field, identifies this with least extensional
representatives among all earlier ordinary indices. -/
namespace LogicLineages.ComputabilityKnowledge.PredictionRetainedScan
open PredictionCanonicalList

def RetainedScanEligible (i : Nat) : Prop :=
  TotalNat (codeAt i) ∧ ∀ j : Nat, j < i → Representative j →
    ¬SameFunction (codeAt j) (codeAt i)

end LogicLineages.ComputabilityKnowledge.PredictionRetainedScan
