# Paper 16: exact directed local seen-list scan

## Literal source slice

`16-persistent-marking-termination-ordering/sections/ordinals.tex` 70–77
describes effectively enumerable finite primary classes and the option of a
least-code representative. The exact executable slice here is
`NumberedWindowClassAlgorithm.advance`, lines 8–9:

```lean
vertices.filter (fun v => seen.any (fun w => w == v || edge w v))
```

Only the per-candidate `seen.any` is implemented here. The same old ordered
`seen` is read for the same candidate v; equality is a stutter and the edge
is directed from old occurrence w to v. No vertex is manufactured. No
append-to-seen, filter over vertices, change to the prior list, inversion of
edge direction, deduplication, round counter, or loop invariant is included.

## Actual scratch and selector tapes

The program is `scan E : Program 4` on `[seen,ctx,ty,v]`, with E an explicit
physical `Program 4` input to the AST constructor. The unchanged original
standard scratch `InternalRawListRecursion.listRec` uses
`constantZero 3` at nil and visits an ordered literal row
`[w,actual tail result,ctx,ty,v]`. The row checks:

- `headEq`: original equality test with physical projections 0,4, hence
  `[w,v]`.
- `edgeCall E`: original composition with projections 2,3,0,4, hence
  `[ctx,ty,w,v]`.
- `scanStep E`: if normalized head equality is one, return literal one;
  otherwise return one if the actual normalized edge call is one. If neither
  is one, return projection 1, the actual recursive tail result. The original
  `normalize` tests **exactly one**, not arbitrary nonzero output of E.

`ExactAllInputDirectedSeen` covers every natural input and every concrete E.
It evaluates against `(decodeNumbers seen).any` of the original ordered
`List.any` with exactly the equality-or-directed-exact-one predicate.
Absent scratch decoding and nil both give zero, including a zero candidate;
a successful zero candidate still needs a genuine occurrence in the list.
Repeated occurrences are not removed. This scratch decoder is not the
separate original polynomial raw field parser.

## Actual arbitrary-open witness and proof plan

`ExactOpenDirectedSeenWitness` gives a real implication in any original
positive body and ordinary context, for arbitrary open seen, ctx, ty, v.
From the **same physical** scan graph at output one it binds a single
ordinary witness w and preserves both the genuine
`scratchMember` unit graph on `[seen,w]` and the object disjunction
`w = v` or the genuine unit E graph on `[ctx,ty,w,v]`.
No decoded-list premise, numerical reflection, runtime validity premise,
or semantic assumption on E occurs in this target.

Possible proof route, not authored: use the original
`actualOriginalListInductionAtCode` with ctx, ty, v fixed as arbitrary open
parameters. `nilRecover` and the actual constant-zero graph exclude success
at nil. `consForward` and `stepCases` expose the actual tail result and
actual step tape in a genuine cons case. Analyze the two exact-one tests
using object-formula cases, original normalization recovery/rejection,
branch elimination, equality acceptance and projection composition.
A successful head case keeps the original w and either its equality or its
actual E graph. When neither head test succeeds, `zeroBranchElim` and value
uniqueness transfer the successful row output to the actual recursive tail
result. Use the induction hypothesis at the same tail and the existing
physical scratch member `headMember`/`tailMember` to carry the same witness
back to the whole input. Those proofs are future suppliers, not dependencies
of the target-only Lean import closure. No earlier expansion AST is reused.

## Later source instantiation and limits

`NumberedWindowScalarAlgorithm.least` passes `edge s ctx ty` to the above
original `advance`. Fix the same Settings and physical slot order for a
later chosen E. Its numeric comparator must pay the original context
carrier: the logical ctx is a real ordered `List Nat`; a physical raw input
requires its actual successful `NumberedWindowFieldAlgorithm.unpack` or a
separately specified graph guard/bridge. Do not infer that an undecodable
context is the real empty context from an implementation default. The
original scalar edge checks guarded exchange and both `admitted` endpoints,
at the same context and requested type; admission in turn checks original
lexical typing and the original window. Those checks are not inferred
internally from a numeric calibration. If a future physical E rejects a
malformed context, that rejects only the edge alternative here: a genuine
same-code equality stutter still succeeds unless an explicit enclosing
guard has rejected the tape beforehand.

This packet claims neither a chosen original scalar E nor its internal
guard/correctness. It says nothing about the absence of witnesses at a
rejected open scan, witness-to-scan completeness, `vertices.filter`,
iteration, directed-round provenance, complete least, output carrier,
RawMatching, or numbered accessibility.
