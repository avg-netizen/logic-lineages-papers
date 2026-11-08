# Parameterized original result-fold calibration: frozen prerequisite

This packet freezes four external natural-number semantic targets for the
existing parameterized result-stack programs. It supplies definitions and
comparators only. Independent frozen-byte review, comparator-only native
preflight, proof authorship, exact aliases and actual axiom audits remain
separate gates. No numbered paper statement is promoted.

## Original source and purpose

Paper 06, `06-godel-t-termination-ordering/paper.tex`, lines 537-549, gives
the original well-typed numbered reduction rules. Lines 551-556 retain the
primary-equivalence quotient, least-code representatives and arithmetic H/R;
lines 558-560 state `lem:id1`, the arithmetic accessibility lemma. This
component is an implementation prerequisite for that work, not a replacement
of the source relations or a completion of the lemma.

The accepted original `InternalApplicationResultFoldCalibration` supplies
an independent well-founded fold, complete state meaning, meaning invariance,
the original work-weight termination bound, terminal padding and completion
of one visit. Those theorems quantify over arbitrary natural-number callback
functions. They therefore already allow each callback to be sliced at one
fixed external natural parameter. Their definitions, invariants, work weight,
terminal predicate and state encoding need no modification.

## Actual ASTs and unchanged data

The actual callbacks are arbitrary `guard leaf : Program 2` and
`combine : Program 5`. Their exact coordinate orders are:

- G and L: `[original whole packed value, parameter]`.
- C: `[domain, codomain, function output, argument output, parameter]`.

The existing `InternalParameterizedApplicationResultStack.transitionP`,
`iterateP`, `runP` and `foldP` are reused literally. `iterateP` is the existing
`InternalParameterizedNumericIteration.repeatP` applied to `transitionP`.
That iterator carries the parameter outside the original state and returns
the original state coordinate, not its outer carry pair.

The original `State`, `encodeState`, status, work frames, result entries,
source/list codecs, initial state and output selector are unchanged. The
original result stack stores argument before function; C still receives
function before argument. The parameter is never added to an original state,
work frame, result entry or source encoding.

The exact run is still at `fuelValue value = 2 * payloadValue value + 1`.
This is the original term payload, not the whole packed value or the carried
pair. The packed type, the parameter and every computed output contribute
nothing to the budget. No fresh interpreter, recursion primitive, uniform
representability premise or parameter-specialized unary AST is introduced.

## Stable independent semantics and exact success check

`semanticFoldP G L C value parameter` is a literal application of the existing
`InternalApplicationResultFoldCalibration.semanticFold` to

- `fun x => evaluate G [x,parameter]`;
- `fun x => evaluate L [x,parameter]`;
- `fun d e f a => evaluate C [d,e,f,a,parameter]`.

The inherited recursion is well founded on the original term payload. The
definition does not refer to a transition, state iteration, bounded run,
fuel, output selector or success check. It is not defined by the theorem it
is intended to calibrate. Both recursive child calls use the same parameter.
Only original tag two together with exact-one G opens the root. Every other
raw root, including malformed source data and guards returning values other
than one, uses L on that same whole packed root.

`goodRunP` is one finite Program 2: the original
`InternalApplicationCertifiedResultFoldClosure.goodState` composed with the
actual `runP`. The reused state check requires status exactly one, empty work
and exactly one result. A singleton containing zero passes; an empty result
stack does not. A nonempty worklist, non-one status or nonsingleton results do
not satisfy the check. This is neither a nonzero-output test nor a constant
one program. Only its separately stated external calibration has value one
on every input.

## Four exact targets

0. **Original semantic fold equation.** For every actual G/L/C and every
   natural value and parameter, the independent fold obeys the original
   tag-two/exact-one opening equation, with original children and original
   domain/codomain. C receives the two semantic child outputs in the required
   order. Fallback uses the same whole root and parameter.
1. **Encoded iteration.** For every count, including zero, every original
   structured state and every parameter, evaluation of the actual `iterateP`
   equals the complete original encoded `stateIterate` with sliced callbacks.
   Non-one statuses, malformed frame tags, short finish stacks and arbitrary
   entire result lists are included. No generated-state or success premise
   occurs. This target is about complete encoded structured states; the
   already checked transition evaluation separately quantifies over every
   raw numeric state without a decoding premise.
2. **Exact bounded run and fold.** For every raw original value and parameter,
   the actual `runP` at its original fixed fuel is exactly
   `encodeState (State.mk 1 [] [semanticFoldP G L C value parameter])`, and the
   actual `foldP` returns that semantic result. There is no callback
   correctness, source-validity, output-size, positive-output, successful-run
   or internal-derivability premise. Zero semantic results are included.
3. **Actual goodRun calibration.** For every raw value and parameter, the
   original whole-state check composed with `runP` evaluates to one. This
   follows externally from the exact singleton shape, not from treating a
   raw fold output or a Boolean status alone as evidence of completion.

All four propositions are external equalities over Nat. No object-language
formula, symbolic graph derivation, arbitrary-context proof or truth-to-
derivability reflection is asserted by them.

## Accepted suppliers and later proof route

The checked parameterized transition evaluation supplies equality with the
original `transitionValue` for G/L/C sliced at p in those exact coordinate
orders. The checked parameterized numeric iteration evaluation supplies
iteration of that very binary AST at fixed p. The original encoded-state
transition theorem then relates the result to the existing `stateStep` and
`stateIterate`.

The accepted original meaning invariant, work-weight decrease, sufficient
fuel and terminal-padding theorems apply directly to those sliced Nat
callbacks. The accepted single-visit completion theorem is the intended
supplier for the exact final singleton at the original fuel. Existing
original initial/fuel/output evaluations and `goodStateSingletonEvaluation`
retain their literal inputs, including a zero singleton result. These
interfaces are pinned as suppliers; they are not copied, generalized by a
new assumption, or re-proved in this specification packet.

This external route deliberately does not depend on the active parameterized
result-stack composition proof. That packet owns internal work append and
result framing. Its compiler admission remains exclusive. No files from
that active component, no mutable proof output, and no pending theorem from
it are used as a supplier here.

## Freeze and verification boundary

`FROZEN-SOURCE-PINS.json` pins the three new Lean specification files and
this correspondence. `SOURCE-PINS.json` pins their full local import closure,
selected accepted supplier roots, the original manuscript, configuration
and stable supplier freeze manifests. These hashes record exact source
inputs, not a new native build or acceptance receipt. Already recorded
supplier source maps are compared with current source bytes separately.

`STATIC-CHECKS.json` records source-shape, delimiter, exact alias coverage,
semantic-independence, callback-coordinate, original-AST/fuel reuse, import
closure and hash checks. Static checking is not Lean elaboration. No new
proof files or theorem bodies are supplied, no compiler is launched, and no
compiler slot is requested or held by this packet.

Any later native check requires explicit sole-slot admission and the existing
`scripts/check.py` entrypoint with unchanged 2048 MiB heap, 1536 MiB process-
tree RSS, 2048 MiB minimum free memory, one thread, 90 CPU seconds and 180
wall seconds, using only the pinned upstream cache. The hard cutoff is
2026-11-08 18:00 UTC. Only `propext`, `Classical.choice` and `Quot.sound` are
permitted theorem axioms.

## Exclusions

This packet does not prove internal unconditional goodRun acceptance,
parameterized internal recursive fold/constructor closure, canonical leaf
selection, representative identification/congruence, uniform canonical or
path correctness, unconditional `CertifiedApplicationLift`, constructor/
lambda/substitution closure, all-term accessibility or paper06 `lem:id1`.
No claim about an untouched work suffix after a padded first run is made.
No original source, accepted theorem, global register, dependency, CI or
resource policy is changed. No Git, publication, full-root build or remote
CI action is taken.
