module
public import LogicLineages.OrdinalComparison.PositiveSourceDomainDefinitions
public import LogicLineages.OrdinalComparison.OneVariableComparisonDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Literal validity of raw numerical kernel entries. NF exponent zero is
excluded; successor and limit exponents are both genuine kernel inputs. -/
def comparisonRawKernelEntriesValid (word : List (Nat × Nat)) : Prop :=
  ∀ p∈word, rawNormalCode p.1=1 ∧ p.1≠0

instance (word : List (Nat × Nat)) : Decidable (comparisonRawKernelEntriesValid word) :=
  inferInstanceAs (Decidable (∀ p∈word, rawNormalCode p.1=1 ∧ p.1≠0))

/-- Whole actual two-sort source IMAGE recognizer. The round-trip list check
prevents an invalid list code from being accepted through a default decoder. -/
def encodedComparisonSourceDomain (n : Nat) : Nat :=
  if n%2=0 then (encodedPositiveSourceData (n/2)).1
  else let p := (n/2).unpair
    let word := (Encodable.decode (α := List (Nat × Nat)) p.1).getD []
    let data := encodedPositiveSourceData p.2
    if word≠[] ∧ Encodable.encode word=p.1 ∧ comparisonRawKernelEntriesValid word ∧ data.1=1 ∧ data.2=1
    then 1 else 0

end LogicLineages.OrdinalComparison
