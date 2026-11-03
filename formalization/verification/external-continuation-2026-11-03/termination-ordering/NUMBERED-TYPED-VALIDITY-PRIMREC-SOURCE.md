# Primitive-recursive success of the actual typed decoders

Paper06 lines551–556 requires computable auxiliary syntax classes and arithmetic
relations on least-code representatives. This component proves effectivity of
the existing typed decoder success predicates under the accepted literal Code
and finite-type presentations. The comparator refers to the actual mutual
`decodeTerm` and `decodeArguments`, their composition with `decodeCode`, and the
original `decodePackedNumber` including its validation filter.

For every fixed finite signature size and actual arity function, the five targets
require primitive recursiveness jointly in the original context, expected type
or ordered type list, and syntax Code or natural input. No primitive-recursive
arity, expansion, validity, or fuel-bound premise is added. Finite arity
effectivity, request expansion, and bounded evaluation are constructive suppliers
with their own checked interfaces. All malformed and ill-typed inputs and the
empty finite signature remain covered.

The proof route uses the accepted numeric fuel bound and exact evaluator
calibration, then the previously checked numeric validation equations. The new
claims concern Boolean success; primitive-codable dependent typed output is a
separate presentation component. Full step-checker effectivity, arithmetic
representation, ID1 accessibility and whole source06 statements are not promoted.

The target SHA-256, recorded before candidate proof authoring, is
`ab9da40aa365ce15da025187a5008b9b1fb8c6112aded84157c372f36bfb5bdc`.

## Accepted verification

The fixed statement gate and the fifteen-target focused aggregate passed
with actual transitive axiom audits. Frozen semantics and comparison hashes
are unchanged. See [the prospective freeze](TYPED-PRIMREC-FREEZE.json) and
[the acceptance record](TYPED-PRIMREC-ACCEPTED.json) for exact source hashes,
compiler evidence, permitted axioms and verification scope.
