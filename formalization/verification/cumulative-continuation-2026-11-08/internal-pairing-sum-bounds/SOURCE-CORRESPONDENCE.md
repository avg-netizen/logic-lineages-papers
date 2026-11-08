# Original internal pairing sum and application fuel

This supporting packet supplies arithmetic needed by the original bounded
application-validity constructor. It does not promote paper06 `lem:id1` or any
numbered statement. The original source is
`../06-godel-t-termination-ordering/paper.tex`, lines 537–549 (typed auxiliary
application and function-side reduction), 551–556 (arithmetic quotient), and
558–560 (`lem:id1`).

## Exact arithmetic and graph semantics

The graph is the unchanged `InternalPairing.pairing` Program, whose actual
branches are `y*y+x` when x<y and `x*x+x+y` otherwise. It is the literal original
Nat.pair AST, not the different Gorbow pairing or a new coding convention.
Every target constructs a genuine `InternalCalculus.Derivation body []` for
arbitrary positive operator body, variable type, and symbolic arithmetic terms.
The conclusion is an implication from original internal graph formulas.
There is no natural-number evaluation hypothesis, no graph semantics-to-proof
reflection, no primitive-recursive representability choice, and no added
axiom, rule, or internal sufficient-fuel premise.

`weakBound lower upper` is exactly `InternalLessThan.strictLess lower (succ
upper)`, and that predicate is the original arithmetic embedding of
`OrdinaryArithmetic.lessFormula`. Thus it expresses the ordinary weak bound
without introducing a new order relation.

The first target strengthens the existing separate coordinate bounds to
`x+y <= p` from the original graph `pairGraph p x y`. It must cover zero and
all arbitrary symbolic inputs, including both branches of the original pair.
The planned arithmetic suppliers are the accepted internal square-self weak
bound, internal additive order laws, both original pairing branch equations,
and original graph value uniqueness. They are proof ingredients, not new
hypotheses in the frozen target.

## Application witnesses and exact fuel

The other two targets share the exact three internal graph witnesses

- `pairGraph payload 2 middle`,
- `pairGraph middle d children`,
- `pairGraph children fp ap`.

This is the literal original payload `pair 2 (pair d (pair fp ap))`, already
used by `InternalApplicationCertificateConstructors.packedApplication` and
`InternalApplicationValidityStack.applicationValue`. The same intermediate
terms occur throughout the conjunction. The sibling constructor-closure
worker confirmed these original nested graph witnesses are sufficient; its
application transition already queries them. No new selector extraction or
external equality premise is required.

The second target bounds `addTerm (succTerm fp) (succTerm ap)` by `payload`.
These are exactly the two child validator counts. Algebraically it is the
bound `fp+ap+2 <= payload`, but the frozen term is the stated child-count sum.
The third target takes the successor on both sides: one step opening the
parent plus those two child counts is at most the original parent count
`payload+1`. It is intentionally the count shape consumed by front-successor
and addition fusion for the original numeric iterator.

The outer packed code and type codes are absent from the bounds. In
particular, reconstructing a function child's arrow type can increase its
packed code. No type-code size, decoding, typing, universe-membership,
canonical-representative, source-window, or input-validity assumption is added.
The original domain `d` is completely arbitrary.

## Freeze and boundary

Definitions, Targets, Preflight, and this correspondence are frozen before
proof authorship. Independent specification review and the coordinator's
serialized native preflight must pass before any candidate proof is authored.
The frozen manifest pins original arithmetic, graph, pair/unpair and intended
application consumers. Existing frozen sources and shared registers are not
edited. All later native runs must use the existing checker with unchanged
2048 MiB heap, 1536 MiB RSS, 2048 MiB minimum free, single-worker and time caps.

This packet does not prove iterator worklist sequencing, internal sufficient
fuel or application-validator closure, original representative congruence,
CertifiedApplicationLift, the joint-context or outer path wrappers, or the
multiset/constructor/lambda/fundamental and all-term ID1 endpoints. External
bounded-validator calibration is a separate result and cannot discharge any
of these internal targets. No full-root build, remote CI, or publication is
claimed.
