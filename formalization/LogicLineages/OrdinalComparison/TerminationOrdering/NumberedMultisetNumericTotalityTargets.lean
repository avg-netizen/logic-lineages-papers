module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericTotalityTargets
open NumberedMultisetNumeric

/-- The existing fuel bound succeeds on every raw natural code, without an
encoding or successful-decoding premise. -/
def ActualNaturalListParserTotality : Prop :=
  ∀ (fuel value : Nat), value < fuel →
    ∃ xs : List Nat, numbersParse fuel value = some xs

/-- The literal source decoder returns exactly one natural list on every
input. This says nothing about typed packed-term or certificate validity. -/
def ActualNaturalListUniqueDecoding : Prop :=
  ∀ value : Nat, ∃! xs : List Nat, decodeNumbers value = some xs

/-- The original successor/pair list encoding covers all natural numbers. -/
def ActualNaturalListEncodingBijection : Prop :=
  Function.Bijective numbersNumber

def ActualNaturalListDecoderEquation : Prop :=
  ∀ (value : Nat) (xs : List Nat),
    decodeNumbers value = some xs ↔ numbersNumber xs = value

/-- Every list length is bounded by its literal numeric code; each entry is
strictly smaller than that code, including entries in arbitrary tail positions. -/
def ActualNaturalListCodeBounds : Prop :=
  ∀ xs : List Nat,
    xs.length ≤ numbersNumber xs ∧ ∀ entry ∈ xs, entry < numbersNumber xs

/-- Exact success criterion for the unchanged fuelled parser. The final nil
inspection consumes one unit, so a list of length k requires k+1 units. -/
def ActualNaturalListParserEquation : Prop :=
  ∀ (fuel value : Nat) (xs : List Nat),
    numbersParse fuel value = some xs ↔
      numbersNumber xs = value ∧ xs.length < fuel

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericTotalityTargets
