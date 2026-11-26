# Paper 16: exact numerical directed rounds on a supplied ordered pool

## Literal source and physical round tape

`16-persistent-marking-termination-ordering/sections/ordinals.tex` 70–77
uses finite effectively enumerable primary classes and optional least-code
representatives. This target supplies only the numerical ordered `rounds`
and `members` of `NumberedWindowClassAlgorithm`, lines 8–16, with an actual
given edge program E and an actual given pool. It does not synthesize the
pool from a term, install an original fixed scalar edge, or select a least
code.

The round input is exactly [fuel,vertices,ctx,ty,seed] on the existing
primitive-recursive syntax. For the zero round the actual two-field
`consCode` on [original seed,zero] produces the literal standard scratch
singleton. `roundBase` runs the same physical `DirectedFilter.pass`,
with a constant-zero arity-four edge, on [vertices,singleton,ctx,ty].
Thus the source filter is exactly `seed == candidate`, including every
equal occurrence, and never inserts a seed missing from the supplied
vertices. A genuine zero-valued seed is still an actual singleton entry,
not nil. There is no independent seed admission assumption.

The step of the actual `.recursion` has tape
[counter,actual preceding result,vertices,ctx,ty,seed]. Projections
2,1,3,4 feed the same physical `pass E`, on
[the *unchanged supplied vertices*,the actual preceding result,ctx,ty].
In particular neither the numerical counter nor the preceding result
replaces the supplied vertices, and nothing is appended to the prior
result. The retained E sees precisely [ctx,ty,w,v] in the original
direction and is tested for output exactly one. The same E, context,
type and pool remain through every successor. Every pass preserves
the input pool's order and each qualifying duplicate.

## Exact supplied-pool targets

`ExactAllInputDirectedRounds` compares that actual Program5 on every
given E and raw Nat tape to
`numbersNumber (NumberedWindowClassAlgorithm.rounds …)`, taking the
original vertices from `(decodeNumbers vertices).getD []`. This is the
standard Nat.pair scratch list, not the original sparse polynomial field
codec; the existing `decoderTotality` ensures every natural scratch
code decodes. The numerical Option branch is kept explicit. Comparison
requires neither original context validity nor window/seed admission.
The proof route is natural induction on the actual fuel evaluation,
with the exact physical directed filter numerical contract and
`consEvaluation`/scratch round trip for the true seed singleton.
Use the previous round's *actual encoded whole list* equality and the
original `numbersRoundTrip` to identify the seen list; replacing it by
extensionally equal set membership would lose order or duplicates.

`ExactAllInputDirectedMembers` additionally feeds the actual
`selectedFuel` from the original input vertices at slot 0 to the same
physical rounds program. `poolLength` is the original scratch
`listRec` with literal zero base and actual successor of the prior
result in row slot 1. Numerically it gives the full supplied ordered
list length by original listRec evaluation, even at repetitions or
empty input. This exact physical length, not code size, a chosen bound,
or a number of distinct values, matches original `members`.
A later proof can use the resulting length equality and the already
paid rounds equation. No additional proof supplier is imported as part
of this target-only closure.

## Scope held back

The optional-minimum part of `ClassAlgorithm.least` is deliberately
absent. The actual `scratchMinimum` AST exists, but the retained
ordered-minimum numeric packet has only a private scratch lemma and its
public exact target concerns the separate raw-parser wrapper; that
wrapper's numeric equality is not a ready public standard-scratch
minimum theorem at this tape. No implicit proof transfer, sparse parser
bridge, arbitrary-open induction/round provenance, original fixed
context edge installation, synthesized cover, RawMatching or numbered
result is claimed.
