# Original application result stack: output-preserving composition

This is a four-target supporting packet for paper 06, `lem:id1`. It freezes
statements only. Independent review and native preflight must precede proof
authorship. It does not change any existing frozen source or prove the
recursive representative fold, representative congruence, or accessibility.

## Source and unchanged computation

The fixed subtype-closed finite type set and auxiliary application rule are
in `06-godel-t-termination-ordering/paper.tex`, lines 537–549. The original
least-code representatives and quotient edge are at lines 551–556; the
arithmetic accessibility lemma is at lines 558–560. These targets supply
execution composition needed for the concrete result-producing machine,
not a reformulation or completion of those source claims.

The imported `InternalApplicationResultStack.transition` and `iterate` ASTs
are unchanged. Their parameters remain arbitrary `guard leaf : Program 1`
and `combine : Program 4`. The transition opens only the exact-one guard
at the original packed root with constructor tag two. It visits function
before argument, retains the original domain and codomain in the finish
frame, and calls combine on `[domain,codomain,functionOutput,argumentOutput]`.
No output tag, representative property, size bound or validity predicate is
added. The arbitrary leaf sees the whole original packed input.

Original pairing and successor/pair raw-list programs remain unchanged.
`InternalApplicationValidityStackAppend.append` is reused literally for
both work and result stacks. Its original nil/cons laws are reusable;
its Boolean successful-work composition theorem is not an output theorem.

## Exact successful-run formula

The only new AST is `liveState : Program 2`, with input order `[work,results]`:
`pair 1 (pair work results)`. It is written using the already exposed
original-pair constructor AST `InternalApplicationResultStack.liveOf`.

`actualRun guard leaf combine count work initialResults finalResults` is
an object-language formula with two existential state witnesses. Its outer
witness is constrained by the actual `liveState` graph at `[work,initialResults]`.
Its inner witness is constrained by the actual `emptyState` graph at
`finalResults`, namely `pair 1 (pair 0 finalResults)`. The actual frozen
`iterate guard leaf combine` graph connects the two witnesses at `count`.
The inner witness is the output, and the outer witness is the initial-state
input of the iterator. No semantic execution relation is substituted.

In particular, the terminal state depends on the entire final result code.
It is not the constant two used by the older Boolean stack. All four
arguments remain arbitrary symbolic arithmetic terms. Empty or nonsingleton
results are permitted. No external decoding, evaluator correctness or
well-formedness premise is hidden in this formula.

## Four frozen targets

1. Terminal iteration: from the original empty-state graph, the actual
   iterator at any count has output exactly the same whole state.
2. Run zero: success at count zero is equivalent to initial work zero and
   equality of the entire final and initial result codes.
3. Work append: if `frontWork` runs from `initialResults` to `middleResults`
   in `first` steps and `suffix` runs from `middleResults` to `finalResults`
   in `second` steps, their actual appended work runs from `initialResults`
   to `finalResults` in the literal arithmetic count `first + second`.
4. Result suffix framing: a successful run is preserved at the SAME count
   and work when the SAME arbitrary background is appended to both its
   initial and final result stacks using the actual original append graph.

Every conclusion is an internal `Derivation body []` for arbitrary
`body : Positive (Fin 1)`, variable type, symbolic terms, and actual finite
Program parameters. These are not standard-model truth assertions.

## Why the restrictions matter

A prefix may finish before its stated count. On attached work, the suffix
can then begin early. Therefore the third target deliberately does not
claim that the suffix is still untouched at the first count. A prospective
proof must handle empty work and arbitrary terminal padding. The exact
final result stack, not merely live status or acceptance, must be preserved.

An underflowing finish can fail with a short result stack but succeed when
background results are appended. Therefore unconditional transition
framing is false. The fourth target is conditional on an actual successful
run: failure is absorbing and cannot reach its live terminal witness.
Its prospective induction must exclude failure and underflow internally.
No result-stack nonemptiness assumption is added, even when the initial
stack is zero; success itself supplies the required exclusion.

The original empty-work transition law, numeric iteration zero/fixed-point/
fusion laws, original list decomposition and append nil/cons laws can
support a later proof. Any such proof must use actual graph derivations and
internal induction, never external calibration reflected into derivability.

## Excluded claims

This packet does not assert recursive fold equations, universal successful
fold output shape, representative calibration/congruence, typed application
closure, a sufficient parent-fuel theorem, `CertifiedApplicationLift`, the
complete paper 06 lemma, or a numbered-statement promotion. It does not
assert intermediate suffix equality, unrestricted failed-run framing,
minimal completion times, or result bounds. No proof author, compiler,
whole-root build, remote CI or publication has run for this packet.
