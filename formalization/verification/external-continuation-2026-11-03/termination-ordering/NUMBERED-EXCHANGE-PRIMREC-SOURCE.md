# Primitive-recursive original finite-neighborhood exchange test

Paper06's computable finite primary-class construction at lines551–556 needs
an effective edge test before finite saturation and least-code selection. The
original executable edge is `NumberedExchangeNeighborhood.exchangeTest`, which
tests membership in the actual recursively generated `neighbors` list. These
targets preserve that Boolean exactly, uniformly in both finite window lists
and both packed typed inputs for each finite signature, arity and binder context.

## Exact comparison

`ActualPackedCalibration` compares the new structural checker directly with the
original `exchangeTest` for every symbol type with decidable equality, every
arity and context, arbitrary window lists, and every pair of packed typed terms.
It has no subtype-closure, universe-membership or effectiveness hypothesis.
`ActualCodeExchangePrimitive` requires primitive recursion on every raw code
pair, including malformed argument spines. `ActualExchangeTestPrimitive`
requires primitive recursion of the unchanged original Boolean on its genuine
packed presentation.

The raw argument projection retains each entry's explicit type together with
its term code. A malformed argument spine returns `none`; successful lists use
the literal permutation relation, retaining multiplicities. The common root
guard requires the source head's original `HeadInWindow`, membership of the
target head code in the literal `sourceHeads arity symbols S` enumeration, and
the original head-equivalence predicate. Target enumeration membership is not
replaced by `HeadInWindow`: that replacement needs subtype closure, while the
effectivity targets cover arbitrary windows.

Ordinary root exchange also compares the decoded head-result types. Numbered
root exchange retains the original label, explicit result, extra-type list and
extra arguments, and imposes no equality on the two heads' original result
types. Contextual exchange preserves each annotation and unchanged sibling;
recursive base or extra exchange does not acquire an enclosing-head window
guard. Lambda bodies, both application positions, ordinary arguments, numbered
base and extra arguments, and both argument-list positions follow the original
recursion. Variables, bottoms, empty argument lists and mismatched constructors
have no outgoing structural case. Identity permutations remain available, so
the checker imposes no distinctness condition.

The effectivity proof may use the accepted literal code view, original head
signatures and window test, exact source-head enumeration, and primitive
permutation decision. Structural recursion is justified by the accepted strict
decrease of the original code number at each recursive child. No primitive
recursiveness premise or oracle substitutes for the actual edge computation.

These statements establish the finite-neighborhood edge computation. Finite
saturation, original `primaryClass`/`primaryTest`, least representatives and
the remaining arithmetic/accessibility source assertions are separate targets.

## Accepted verification

The fixed statement gate and the thirteen-target focused aggregate passed
with actual transitive axiom audits. Frozen semantics and comparison hashes
are unchanged. See [the prospective freeze](PRIMARY-CLASS-PRIMREC-FREEZE.json) and
[the acceptance record](PRIMARY-CLASS-PRIMREC-ACCEPTED.json) for exact source hashes,
compiler evidence, permitted axioms and verification scope.
