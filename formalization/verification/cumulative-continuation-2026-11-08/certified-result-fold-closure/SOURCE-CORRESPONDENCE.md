# Original certified result-fold constructor closure

This packet freezes three supporting statements for paper 06, `lem:id1`.
Definitions, Targets and Preflight are separate from future candidate proofs.
Independent review and successful native preflight must precede proof
authorship. No existing source or frozen comparator is changed.

## Original source and checked suppliers

The source is `06-godel-t-termination-ordering/paper.tex`: the finite
subtype-closed type set and original auxiliary application rule occur at
lines 537–549, least-code representatives and the arithmetic quotient edge
at lines 551–556, and the accessibility lemma at lines 558–560. This packet
supports later internal application/representative work. It does not prove
that lemma, representative congruence, or the original selected-edge rule.

The original result-stack `transition`, `iterate`, `run`, `output` and `fold`
are unchanged. Function is visited before argument. Finish pops argument
before function and applies combine to exactly
`[domain,codomain,functionOutput,argumentOutput]`. Leaf receives the whole
original raw packed input. The root opens only for original tag two and an
exact-one root guard. All guard, leaf and combine Programs remain arbitrary.

The checked four-target result-stack composition packet supplies whole-state
terminal padding, zero-step runs, output-preserving work append, and result
suffix framing conditioned on a successful run. The original numeric
iteration zero/front-successor/addition-fusion/fixed-point laws and internal
pairing-sum bounds are also checked suppliers. The checked six-target full
fold calibration packet supplies external all-natural-input evaluation and
exact singleton final-state shape, not internal truth-to-proof reflection.

## Concrete success check and exact bridge

`goodState : Program 1` is a new finite AST built only from the original
branch, exact-one, state/list selectors and zero/one constants. It returns
one exactly when the supplied raw state has status one, work zero, a nonzero
result-list code and result tail zero. This accepts the singleton result
zero. It rejects an empty result stack, any residual work, any non-one status
and every nonsingleton result stack. It does not inspect or bound the head.

`goodRun guard leaf combine` is literally `goodState` composed with the
existing `run guard leaf combine`. Its fuel is the unchanged run's own
`2*original-payload+1`, not a new count supplied by the consumer.

`visitWork : Program 1` constructs the original list `[visit value]` with
the original pair and successor/pair list ASTs. `payloadFuel p` is the literal
arithmetic term `succ (p+p)`. `certifiedFold ... y value` is a conjunction of
the actual good-run graph at one and the actual existing fold graph at y.
Neither conjunct is a class field, a semantic relation or an assumed proof
of completion.

The internal bridge has explicit graphs for the right-selector payload,
`visitWork`, and original `consCode singleton y 0`. Under those constructor
graphs, it equates `certifiedFold ... y value` with the checked composition
packet's exact `actualRun` formula at `payloadFuel payload`, singleton visit
work, initial results zero and final results `singleton`. That formula uses
the actual initial live-state and final empty-state constructors and actual
iterator graph. Its final state is `pair 1 (pair 0 singleton)`, so terminal
padding carries the entire result code and does not replace it by a Boolean.

The fold output selector returns default zero on a malformed final state.
Therefore a raw fold graph, even at output zero, is never used alone to
infer successful execution. The success conjunct remains explicit on both
sides of constructor closure. External all-input calibration cannot remove
that conjunct from an internal derivation.

## Generic internal application closure

The constructor premise is the unchanged
`InternalApplicationValidityClosure.applicationConstructors`: the same raw
domain, codomain and payload terms constrain the arrow list, packed function,
packed argument and original packed application. The only additional
premises are the actual root-guard graph at one on the whole parent, both
children's actual `certifiedFold` formulas, and the actual combine graph at
the proposed parent output. No source-validity, typed-result,
representative, output-size or larger-fuel assumption is added.

The target concludes the parent's actual good-run graph at one AND its
existing fold graph at the specified combine output, at the original parent
run's fixed fuel. This is a conditional internal constructor theorem, not
an unguarded internal totality claim. The guard is designed as an explicit,
externally redundant guard for future selected-edge/typed consumers. Those
consumers must still connect it to their original statements or prove the
required internal success facts; this packet does not claim they are done.

A later proof must use the following actual internal execution facts:

1. Apply the bridge separately to both children, with singleton outputs.
2. Frame the argument run by the function's singleton result so argument
   finishes above function. Successful-run framing, not unrestricted
   transition framing, is required because underflow may be repaired by an
   added background stack.
3. Compose the original function visit, argument visit and finish work with
   output-preserving work append. Early child completion may begin the next
   work before the child's full stated count, so no intermediate assertion
   of an untouched suffix is permitted.
4. Use the opening and finish one-step laws and the actual combine graph.
   The count used is one opening step, both child counts and one finish step.
5. Derive that count's bound by `2*parentPayload+1` using internal pairing-sum
   bounds and arithmetic. The original payload bound gives
   `fp+ap+2 <= parentPayload`. Child outputs and reconstructed packed type
   sizes contribute nothing to this bound.
6. Pad the entire empty-work singleton-result state internally to the exact
   parent fuel, using original numeric iteration and terminal-state laws.
   Apply the bridge back to obtain both parent graphs.

These are proof obligations, not assumed fields or supplied conclusions.
They may be split into proof-only helpers after review and native preflight.

## External all-input success calibration

The third target says `evaluate (goodRun guard leaf combine) [value] = 1`
for every natural value and arbitrary actual Programs of arities 1, 1 and 4.
There is no validity, expected type, output bound or calibration premise.
The checked `ActualOriginalBoundedResultFoldCalibration` already computes
the run as exactly `encodeState (State(1,[],[semanticFold value]))`, where
the semantic fold is independently defined by well-founded recursion on
original payload. Evaluating the new state check on that singleton proves
this external consequence. It is not an internal totality theorem and must
never be reflected into an object-language proof.

## Explicit nonclaims

This packet does not assert an unguarded internal good-run theorem, a
malformed-state success theorem, failed-run result framing, an untouched
suffix after padded child execution, output bounds, representative-specific
calibration or congruence, original selected-edge completion,
`CertifiedApplicationLift`, all-term accessibility, or any numbered source
promotion. No proof author, native compiler, full-root build, remote CI or
Git publication has run for this packet at freeze time.
