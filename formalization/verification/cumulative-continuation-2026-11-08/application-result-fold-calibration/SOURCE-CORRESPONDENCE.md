# Original result fold: external semantic calibration

This is a six-target supporting packet for paper 06, `lem:id1`. It calibrates
the complete existing result-stack program against an independent semantic
fold. It does not complete the original representative-application congruence,
internal constructor closure, application-step rule or arithmetic accessibility
proof. No numbered source statement is promoted.

## Original source and unchanged implementation

The fixed subtype-closed finite type set and auxiliary application rule are
in `06-godel-t-termination-ordering/paper.tex`, lines 537–549. Least-code
representatives and the quotient edge are at lines 551–556. The concrete
implementation is the already checked `InternalApplicationResultStack`
packet. Its definitions, targets, guards, frames, encodings and finite
program ASTs remain byte-for-byte unchanged.

An original application remains `pair e (pair 2 (pair d (pair fp ap)))`.
Its original typed children are `pair (1 + pair d e) fp` and `pair d ap`.
All selectors are total on arbitrary natural input, without a successful
term decode or a validity premise. The original pair and natural-list codecs
are unchanged. Only implementation frames/state use the already frozen
result-stack private representation.

## Independent mathematical specification

For arbitrary total functions `G`, `L` and `C`, the semantic fold `F` is
defined by well-founded recursion on the original term payload:

- If the original root constructor tag is two and `G(raw) = 1`, return
  `C(domain, codomain, F(functionChild), F(argumentChild))`.
- Otherwise return `L(raw)`, with the whole original packed input unchanged.

The recursive definition mentions neither the transition, iterator, run,
output selector nor any fuel. Its only termination argument is the already
checked original bound `functionPayload + argumentPayload + 2 <= payload`.
Both recursive payloads are therefore strictly smaller. Reconstructed type
codes and every computed output may grow arbitrarily; packed-code descent
and output-size bounds are not assumed.

The small `decreasing_by` script in Definitions is solely the termination
certificate needed to state this independent total function. It invokes the
accepted payload bound and child-selector equations; it does not prove any
calibration, machine invariant or target theorem.

## Semantic configuration invariant

The finite-list denotation is structurally recursive on the pending worklist.
A visit pushes `F(raw)` immediately. A finish pops argument then function and
pushes `C(domain, codomain, function, argument)`. Unknown frame tags, short
finish stacks and non-one state status denote failure. Empty live work denotes
the entire result stack.

This denotation never expands a visit or creates work frames, so it is not
a renamed execution of the result-stack machine. The one-step invariant must
be proved from the independent recursive fold equation, including the two
visits and finish introduced by an opening transition. Its iterated form
then preserves every result value and its order.

## Six exact obligations

1. The semantic fold's all-raw-input recursion equation, with exact-one root
   guard, original typed children and fallback on the whole original root.
2. The actual existing numeric iterator equals encoded structured execution
   for every count and every structured state, including malformed frames,
   non-one status and finish underflow. The whole final state is compared.
3. The existing work weight is sufficient on every live state. An extra step
   covers arbitrary status. Failed or live empty-work states are fixed under
   all further iterations, retaining any result stack.
4. The independent complete configuration denotation is preserved by one
   actual transition and by every count of structured execution.
5. A single original visit, with any background result stack and any count
   at least `2 * originalPayload + 1`, ends live with empty work and pushes
   exactly `F(raw)` onto the unchanged background result stack.
6. For arbitrary finite `G : Program 1`, `L : Program 1`, `C : Program 4`
   and every natural input, the actual bounded run returns the exact encoded
   singleton state and the actual fold returns the independent semantic fold.

The single-visit completion target deliberately has no work suffix. The
existing bounded fuel may contain terminal padding; adding a work suffix
can let it start early. This packet makes no false intermediate-state or
untouched-work-suffix claim. The separate internal result-stack composition
packet addresses successful sequential runs with their appropriate contract.

The budget is exactly the existing `2 * payload + 1`. Visit and finish each
cost one. The checked opening budget covers both child visits and finish;
results contribute nothing to work weight. No raw packed-code or result-size
bound is introduced. All-input calibration includes nonapplications,
malformed source encodings and root guards returning values other than one.

## Boundary and next use

These are external natural-number semantic statements about the existing
AST. They do not reflect standard-model truth into the internal calculus.
They assume no internal recursive-fold equation or representative property,
and do not establish either. Representative-specific calibration still
requires the original valid-window/source-universe and representative
congruence facts, with nonuniverse and malformed-input behavior preserved.
Internal result-stack composition and subsequent internal constructor
closure remain separate obligations. No original least-code representative,
window condition, type guard, context quantifier or quotient relation changes.

The packet is frozen before independent specification review and native
preflight. No new target proof author or compiler has been started for it.
No Git action, publication, full-root build or remote CI is claimed.
