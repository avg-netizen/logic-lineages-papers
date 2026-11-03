# Primitive-recursive original primary-class candidate lists

Paper06 lines551–556 asserts finite computable primary classes before taking
least-code representatives. These two fixed targets establish primitive
recursiveness of the original `classCodes` and `classCandidates` algorithms,
jointly in both window lists and the actual packed input for every fixed
finite signature, arity and binder context.

The exact bounds remain the original term `size`, original `maxLabel`, context
length, and twice the original size as enumeration fuel. The output root type
is the original packed type. The source-head list retains the original
`headWindow` enumeration and filtering. Ordered constructor groups, duplicate
occurrences, bounded extra-type lists, and binder-bound increments are retained.
The candidate list is exactly the original structural list filtered by the
original dependent typed decoder.

Both algorithms remain defined on arbitrary windows and inputs, with no
subtype-closure or input-universe premise. They are the existing finite candidate
overapproximation. Their effectivity does not itself prove primitive recursion
of exchange testing, saturated primary classes, least representatives or the
canonical carrier. Those operations and formal arithmetic/accessibility claims
remain separate obligations.

## Accepted verification

The fixed statement gate and the sixteen-target focused aggregate passed
with actual transitive axiom audits. Frozen semantics and comparison hashes
are unchanged. See [the prospective freeze](CLASS-CANDIDATES-FREEZE.json) and
[the acceptance record](CLASS-CANDIDATES-ACCEPTED.json) for exact source hashes,
compiler evidence, permitted axioms and verification scope.
