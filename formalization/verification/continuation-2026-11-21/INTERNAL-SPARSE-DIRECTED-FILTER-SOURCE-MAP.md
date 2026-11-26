# Paper 16: one exact directed ordered filter pass

## Literal original source and carrier

`16-persistent-marking-termination-ordering/sections/ordinals.tex` 70–77
uses the actual finite effectively enumerable primary classes and optional
least-code representatives. The full executable at issue is
`NumberedWindowClassAlgorithm.advance`, lines 8–9:

```lean
vertices.filter (fun v => seen.any (fun w => w == v || edge w v))
```

This is one pass. It is not `rounds`, its zero/seed filter, pool-length
iteration, or `List.min?`. It is not the Paper 16
`NumberedWindowPositivePathAlgorithm.advance` (an option-state transition on
one tag-two positive-path certificate and raw/least calls). Nor is it the
older `PrimaryExpansion.expand`, which appends a filtered pool to the
already reached list. There is no append of seen elements in this target.

`pass E : Program 4` reads `[vertices,seen,ctx,ty]` with E an explicit actual
`Program 4`. It uses original standard-scratch `listRec`, whose nil is
literal zero. The physical step reads `[v,rest,seen,ctx,ty]`: current input
head v, actual **output of the same pass on the input tail** rest, and the
three unchanged original parameters. The `scanHead E` projections
2,3,4,0 call the existing actual directed scan on `[seen,ctx,ty,v]`.
That scan calls E as `[ctx,ty,w,v]`, not the reverse. Normalize its output
by the original exact-one test. The zero branch is projection 1 (rest).
The accepting branch applies the actual `InternalListCodec.consCode` to
projections 0,1 (v,rest). Thus right-fold preparation and prepending
preserve order and retain every accepting input occurrence, including
repeated equal values, with no deduplication or sorting. Rejection emits
no new occurrence. The seen tape is never replaced by rest or by a
growing output list.

## Separately exact numerical and object targets

`ExactAllInputDirectedFilter` compares the actual program on **every Nat
and supplied E** to `numbersNumber (NumberedWindowClassAlgorithm.advance …)`
on the original decoded ordered vertices and seen lists. The comparator's
edge callback is literally evaluation of E at `[ctx,ty,w,v]` equal to one;
the equality stutter remains the source `advance`'s own predicate. Both
scratch decoders use the explicit original `getD []` option convention.
`NumberedMultisetNumericTotalityProof.decoderTotality` supplies that every
natural standard-scratch input does have an exact decode; this is NOT a
claim that a malformed original sparse polynomial raw field succeeds.
Nil vertices emit coded nil; nil seen retains no vertices. The original
context/type fields are passed unchanged even when symbolic or not
admitted; any such validation belongs to a separately installed edge or
outer gate. Independent numerical route: exact directed scan evaluation,
original listRec all-input evaluation, physical row projection,
conditional/normalizer evaluations, `consEvaluation`, and the literal
`List.filter_cons` equation. No open assertion is derived from this route.

`ExactOpenDirectedFilterCons` is a genuine implication in the original
calculus at arbitrary body, ordinary context, and open terms. Its
antecedent is the real cons graph of the input vertices at (head,tail)
conjoined with the actual physical pass graph on those vertices at out.
Its consequent binds one rest, explicitly the actual pass output at
`[tail,seen,ctx,ty]`. The same rest occurs in exactly the two alternatives:
(1) the actual scan unit graph on `[seen,ctx,ty,head]` and the physical
`consCode` graph producing out from head/rest; (2) the negation of that
same scan **graph formula** and actual equality of out/rest. Its
consequent is not an external membership assumption. It has no
universal rejection-completeness or no-witness result.

Open route to verify later, not authored: original `consForward` and
`stepCases` recover the actual same-tape tail computation and the actual
row output. Case split inside the original calculus on the exact scan
unit graph. Transport this graph into or recover it from the projected
`scanHead E` using original composition proofs at the same slots.
In the accepting case use `normalizeAccept` and `successorBranchElim`,
then recover the primitive cons graph. In the other branch use
`normalizeReject` for this projected graph, `zeroBranchElim`, and the
actual projection value with `valueUnique` for out=rest. This supplies
only a local nonacceptance formula, not scan=0 iff absence of edge
witnesses. Existential introduction packages the actual rest and both
literal selector branches. It requires no directed witness proof or
numeric trace.

The next separate open supplier would use actual output membership
to derive original vertex membership and a same-seen directed
witness, with an output-quantified genuine list invariant and actual
membership nil/cons elimination. This packet does not assert that
supplier, introduce any real scalar E, prove original packed-context
admission, filter/rounds closure, a whole least program, RawMatching,
or numbered accessibility.
