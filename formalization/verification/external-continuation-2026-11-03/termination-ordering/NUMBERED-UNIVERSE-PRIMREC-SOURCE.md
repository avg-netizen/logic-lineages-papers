# Primitive-recursive original finite-universe tests and decoding

Paper06 lines537–556 restricts auxiliary syntax to a finite type window and then
uses computable primary classes and least-code representatives. These five fixed
targets establish effectivity of the original finite-universe membership tests
and filtered numeric decoder under the accepted literal presentations.

Typed term and argument decoder success with universe membership is primitive
recursive jointly in both window lists, binder context, expected type or ordered
types, and structural Code. The actual `rawCarrierTest` is primitive recursive
jointly in both window lists, context and natural input. The original packed-term
`universeTest` and original `decodeUniverse` are primitive recursive jointly in
both window lists and their packed or numeric input, for each fixed context.
The latter decoder returns the actual dependent typed packed syntax.

Every finite signature size and actual arity function is retained, including the
empty signature. No primitive-recursive predicate, arity, traversal or fuel
supplier is assumed. No subtype-closure premise or replacement encoding is
introduced. Failed original parses and unsuccessful universe filters preserve
their original behavior. Primary-class operations, canonical carrier testing,
full step checking, arithmetic representation and accessibility remain separate.

## Accepted verification

The fixed statement gate and the sixteen-target focused aggregate passed
with actual transitive axiom audits. Frozen semantics and comparison hashes
are unchanged. See [the prospective freeze](UNIVERSE-PRIMREC-FREEZE.json) and
[the acceptance record](UNIVERSE-PRIMREC-ACCEPTED.json) for exact source hashes,
compiler evidence, permitted axioms and verification scope.
