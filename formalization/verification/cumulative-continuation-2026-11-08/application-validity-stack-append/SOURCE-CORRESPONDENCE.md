# Original application-validity stack: successful worklist append

This three-target supporting component supplies an internal sequential-success
law for the frozen original application-validity stack toward paper 06,
`lem:id1`. It preserves the actual stack transition and numeric iterator. It
does not establish internal application-validity constructor closure, the
remaining original application-lift assembly, or the numbered paper lemma.
No numbered source statement is promoted.

## Literal original list and stack syntax

`InternalApplicationValidityStackAppend.append` is a concrete arity-two PR
AST with inputs `[prefix,suffix]`. It specializes the already defined original
raw-list recursor:

    listRec (projection (0 : Fin 1))
      (composition consCode [projection 0, projection 1])

The arity-one base returns the suffix. The arity-three step receives
`[head, recursively appended tail, suffix]` and returns the original
`consCode` of the head and recursively appended tail. The suffix parameter is
already incorporated into the recursive output. The original nil code is
zero, and cons uses successor of the original `Nat.pair` program. No host
list, successful decoder, new encoding, recursive relation oracle, or chosen
representability witness replaces this AST.

The stack iterator is imported unchanged from
`InternalApplicationValidityStackDefinitions.lean`. Its inputs are the
numeric count and initial state. Its transition opens an application into
the reconstructed typed function followed by the typed argument, retains the
remaining worklist, and checks the actual node guard at the result type.
For a non-application it delegates the whole packed value to the old leaf.
Both tests accept exactly at one. Failure returns state zero.

The successful terminal STATE is the arithmetic numeral **two**, because
the unchanged encoding of status one and the empty worklist is
`Nat.pair 1 0 = 2`. It is not Boolean acceptance one. The definition
`successState` is exactly `succTerm (succTerm zeroTerm)`.

For arbitrary symbolic terms `count` and `work`, `successfulWork node leaf
count work` is the actual first-order formula

    exists state,
      programGraph pairing state [one,work] AND
      programGraph (InternalApplicationValidityStack.iterate node leaf)
        two [count,state].

The existential state is inside the original object-language formula and
is constrained by the actual original pair graph. This definition is not
an external execution predicate or a new proof-rule premise. It does not
mention standard-model evaluation, decoded terms, leaf calibration, a
well-formedness condition, a weight bound, or semantic term validity.

## Exact frozen targets and full quantifiers

All three conclusions have the form
`Nonempty (InternalCalculus.Derivation body [] formula)` for every arbitrary
`body : Positive (Fin 1)` and every variable type `alpha`. Every numerical
argument below is an arbitrary `OrdinaryArithmetic.Term alpha`, not a
metatheoretic natural numeral. The composition target additionally quantifies
arbitrary actual unary `node` and `leaf` PR ASTs.

1. **ActualOriginalRawListAppendZero:** for every output and suffix,
   the original append graph at `[zero,suffix]` is equivalent to
   object-language equality of output and suffix.
2. **ActualOriginalRawListAppendCons:** for every prefix, head, tail,
   suffix and output, the actual `consCode` graph for the prefix implies
   equivalence between its append graph and one existential appended-tail
   witness. That witness satisfies the append graph at `[tail,suffix]` and
   the actual cons graph with the same original head and output.
3. **ActualOriginalSuccessfulWorkAppend:** for every first count, second
   count, prefix, suffix and joined list code,

       appendGraph joined prefix suffix AND
       successfulWork node leaf first prefix AND
       successfulWork node leaf second suffix
       IMPLIES
       successfulWork node leaf (addTerm first second) joined.

All three antecedents in the third target are object-language formulas
inside the derivation. No external implication to internal truth is used.
The original arithmetic addition term is first count plus second count.
Both counts and all raw list codes are unrestricted.

## Why the composition conclusion is acceptance-only

A successful prefix may have exhausted its worklist before consuming its
entire stated count. When a suffix is attached, execution can begin that
suffix during the prefix's unused fuel. Consequently this packet does NOT
assert that the joined stack equals the untouched suffix at the first
count, or that padding commutes with arbitrary context extension.

The summed-count success statement is the required truthful replacement.
Success is a fixed point of the original transition, so processing a suffix
early does not invalidate success after the full summed count. The target
does not require a first-hit time, a no-padding hypothesis, or an altered
stack machine.

## Permitted proof route, not additional assumptions

The nil/cons equations specialize the existing original raw-list recursion
equations. The internal sequential-success proof may use full-language
natural-number induction on the first count, keeping all worklists and the
second count universally quantified inside its induction formula.

The zero case forces the successful prefix to be empty. In the successor
case an empty prefix is handled by fixed-point padding of the suffix.
A nonempty prefix uses a proved one-step context law: append preserves the
head; application pushes and successful leaf pops commute with attaching
the suffix; rejected guards fail in both executions. The actual failure
state zero is fixed, so its successful continuation is internally
contradictory. Front-successor then reduces to the induction hypothesis.

Every terminal-state, failure, branch, append-context and padding claim in
this route must itself be proved in the unchanged calculus. None is a field
of data or an extra hypothesis of the frozen target. Numeric iteration
zero/front-successor/addition/fixed-point laws may be used through their
actual internal statements. External bounded-validator calibration is not
an internal inference rule.

## Consumer and remaining closure

The intended application consumer first recovers each child validator's
singleton success at its actual payload-plus-one count, then uses this
append theorem and the checked original application push. It obtains
success at `succTerm (addTerm (succTerm fp) (succTerm ap))`. Separate
internal pairing arithmetic must compare that count with the exact parent
payload-plus-one count. An internal difference witness and numeric
fixed-point padding then reach the unchanged frozen fuel.

The validator-acceptance bridge, this consumer assembly, and the actual
`recursiveData` source/target constructor closure remain pending at this
freeze. Raw outer-tag graphs must reconstruct the original child packed
values; packed-number size bounds cannot replace payload bounds. The
universe branch retains its actual result-type membership graph, and the
target branch has no universe filter. Representative congruence, the full
typed-edge/path assembly, `CertifiedApplicationLift`, and the all-term
accessibility endpoint are not claims of this packet.

Paper 06 lines 537-549 give the original auxiliary-application setting and
function-side rule, lines 551-556 its arithmetic quotient relation, and
lines 558-560 the `lem:id1` statement. This packet is a supporting internal
program-calculus lemma, not a replacement formulation of those source rules.

## Freeze and validation boundaries

`FROZEN-SPECIFICATION.json` and `FROZEN-SOURCE-PINS.json` record the exact
definitions, targets, comparator-only preflight, this correspondence,
original list/stack/calculus suppliers and paper source. The already frozen
definitions and targets retain their hashes from the initial two-file
snapshot. This packet adds only new append-family files and evidence.

Independent specification review and bounded serialized native preflight
must pass before proof authorship. Neither has passed for this packet at
freeze time. The preflight module contains only comparator definitions, not
proofs. This worker has not invoked a compiler and has no compiler slot.
Subsequent native checks must use `scripts/check.py` under a fresh sole-slot
grant with the unchanged 2048 MiB heap, 1536 MiB RSS, 2048 MiB minimum-free,
one-thread, 90-second CPU and 180-second wall profile, using pinned upstream
cache only. No full-root build, acceptance, remote CI or publication is claimed.
