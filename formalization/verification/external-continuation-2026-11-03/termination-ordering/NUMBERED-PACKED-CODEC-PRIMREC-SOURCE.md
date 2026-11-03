# Primitive-recursive original packed encoder and decoder

Paper06 lines551–556 requires effective typed auxiliary syntax for primary classes
and least-code representatives. These two fixed targets expose the actual
`packedNumber` encoder and `decodePackedNumber` decoder as primitive-recursive
functions for every fixed finite signature, actual arity and binder context.
The output is the original dependent packed typed term, not merely a successful
validation flag or an untyped Code.

The underlying `Primcodable` presentation uses exactly those numeric functions
and is earned by their original round trip, actual normalization on successful
decodes, and the proved primitive-recursive success predicate. The interface
does not replace a missing theorem with a coding assumption. The signature may
be empty; malformed numeric inputs retain the original rejection behavior.

This establishes packed-syntax codec effectivity. Finite-universe tests,
primary-class operations, full step-certificate checking, arithmetic
representation and accessibility remain separate source obligations.

## Accepted verification

The fixed statement gate and the fifteen-target focused aggregate passed
with actual transitive axiom audits. Frozen semantics and comparison hashes
are unchanged. See [the prospective freeze](TYPED-PRIMREC-FREEZE.json) and
[the acceptance record](TYPED-PRIMREC-ACCEPTED.json) for exact source hashes,
compiler evidence, permitted axioms and verification scope.
