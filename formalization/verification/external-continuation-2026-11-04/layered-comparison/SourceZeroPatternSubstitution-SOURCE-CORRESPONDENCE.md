# Exact zero-pattern substitution

Paper09 hardness.tex lines 179–193 selects zero polynomial unknowns and retains the other indices. This component fixes one finite retained set, represented explicitly as the range of an injective map r:Fin m→Fin n. Its ordering is supplied by r, not inferred or silently sorted.

lookup chooses the unique retained preimage when one exists. ExactIndices proves lookup(r j)=some j, lookup i=none exactly outside the retained range, and exact reextension at retained/omitted coordinates for any zero-bearing value type. No transfinite ordinal is coerced to zero: only an explicitly omitted original variable is assigned zero.

The actual SignedPair.Expression has no zero constructor. substitute therefore replaces omitted variables with .add .unit (.neg .unit), an exactly zero signed difference, while preserving unit, add, neg and shift and reindexing every occurrence through the same lookup. OrdinalMeaningTransport and PolynomialMeaningTransport prove exact equality with the original expression under the zero-extended environment. Repeated occurrences and arbitrary nested syntax are covered by these quantified targets. Empty retained sets and n=0 are included.

The definitions use a mathematical finite preimage choice and make no computability claim. Enumerating all zero patterns, selecting the nonzero pattern from a solution, simultaneous system equivalence, positive admissible lifting, numeric source encoding, and the independent polynomial-system undecidability theorem remain separate. This is not whole functional-hardness and changes no manuscript/register/export.
