module
public import LogicLineages.OrdinalComparison.CollectedClosureBoundsDefinitions
public import LogicLineages.OrdinalComparison.EncodedCollectedNormalizeDefinitions
public import LogicLineages.OrdinalComparison.PositiveInputPlugDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

noncomputable def encodedPositiveZeroBound (n m : Nat) : Nat :=
  encodedCollectedZeroBound [encodedCollectedNormalize n,encodedCollectedNormalize m]

/-- Exact finite enumeration. Values at 0 are deliberately excluded, matching
source inputs 1,...,N-1. No semantic equality test on normal forms is used. -/
noncomputable def encodedPositiveEqualityPrefix (n m : Nat) : Nat → List Nat
  | 0 => []
  | k+1 => encodedPositiveEqualityPrefix n m k ++
      if 0<k ∧ encodedPositiveEvaluation n k=encodedPositiveEvaluation m k then [k] else []

noncomputable def encodedPositiveEqualitySet (n m : Nat) : List Nat :=
  encodedPositiveEqualityPrefix n m (encodedPositiveZeroBound n m)

end LogicLineages.OrdinalComparison
