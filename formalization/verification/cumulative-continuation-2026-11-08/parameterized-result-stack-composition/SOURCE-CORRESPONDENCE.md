# Parameterized result-stack composition: frozen prerequisite

This packet freezes three supporting internal-calculus targets for paper 06
`lem:id1`: zero-step successful execution, output-preserving work append,
and result-suffix framing under actual success. Definitions and comparators
only are supplied. Independent review, comparator-only native preflight,
proof authorship, exact statement checks and axiom audits remain separate
gates. No numbered source statement is promoted.

## Original source and unchanged programs

The original numbered reductions are in
`06-godel-t-termination-ordering/paper.tex`, lines 537-549. Lines 551-556
retain the primary-equivalence quotient, least-code representatives and
arithmetic H/R; lines 558-560 state the arithmetic accessibility lemma.
This is an implementation prerequisite, not a replacement of those source
relations or completion of their mathematical claims.

The accepted original `InternalApplicationResultStackCompositionTargets`
contains terminal iteration, run zero, work append and result-suffix framing.
This packet preserves the actual-run content and all success premises of
the last three. Their unary callbacks are replaced by the already frozen
parameterized stack ASTs at one shared symbolic parameter. The internal
derivations are stated in arbitrary `Gamma`, matching the parameterized
stack interface; setting `Gamma = []` recovers the original context shape.
No extra semantic or callback premise is introduced by this generalization.

The actual callbacks are arbitrary `guard leaf : Program 2` and
`combine : Program 5`, selected before any symbolic arithmetic terms.
The input orders remain **[original packed value, parameter]** and
**[domain, codomain, function output, argument output, parameter]**.
The existing `transitionP` and `iterateP` definitions are reused unchanged.
There is no family of unary ASTs specialized to a parameter numeral.

The original state remains the nested pair of status, original work code
and original result code. `liveState` and `emptyState` are the already
existing programs, not copies or replacement constructors. Their status
is exactly one. Original visit/finish frames, source codecs, selectors,
list encoding and result order remain unchanged. The same original
`InternalApplicationValidityStackAppend.append` AST is used for both work
and result concatenation.

The parameter is not stored in an original work frame, result entry or
result-stack state. `iterateP` passes it through the existing parameterized
numeric iterator as its last input; the iterator's outer carry pair is
not a change to the original state. No new program, state constructor,
measure or fuel is introduced in this packet. The original `fuel` and
`fuelValue = 2 * payload + 1` remain unchanged. The statements concern
arbitrary counts, not a claim that the original fixed fuel always succeeds.

## Exact actualRunP formula

The only new relation is

`actualRunP G L C count work initialResults finalResults parameter`.

It has exactly two internal existential witnesses:

1. The initial state is constrained by the actual original
   `graph2 liveState initialState work initialResults`.
2. The final state is constrained by the actual original
   `graph1 emptyState finalState finalResults`, and by the actual
   `graph3 (iterateP G L C) finalState count initialState parameter`.

The final state's work is zero and status is one because these are the
literal original `emptyState` constructor's coordinates. The entire final
result code is retained, including zero, singleton or nonsingleton stacks.
It is not replaced by a Boolean completion test, a fixed successful-state
constant, or an externally supplied evaluator relation.

Only the two states are existentially quantified. The original free
parameter is weakened through both binders using the same two `Sum.inl`
relabelings as the count and final results. It is never rebound, selected
existentially, or changed between the premise and conclusion. All work,
count and result terms remain arbitrary symbolic raw codes. No decoded-list,
well-formedness, callback correctness or representative premise is hidden.

## Three exact targets

Each target concludes actual
`Nonempty (InternalCalculus.Derivation body Gamma formula)` for arbitrary
positive `body`, original variable type, context, actual callback ASTs and
symbolic terms.

0. **Run zero.** At every symbolic parameter, `actualRunP` with literal
   arithmetic zero count is iff empty initial work and equality of the
   entire final and initial result stacks. This is the original exact
   zero-step characterization, not just a sufficient condition.
1. **Work append.** Assume the actual original append graph for
   `joined = frontWork ++ suffix`, the actual first run from
   `initialResults` to `middleResults`, and the actual second run from
   that identical `middleResults` to `finalResults`. The conclusion is the
   actual run on `joined`, from `initialResults` to `finalResults`, at the
   literal `OrdinaryArithmetic.addTerm first second`. Every run uses the
   same G/L/C ASTs and the same symbolic parameter. There is no parameter
   equality side condition because no distinct parameter is introduced.
2. **Result suffix frame.** Assume an actual successful run and the two
   original append graphs attaching the same `background` to its initial
   and final result codes. The conclusion is the actual run between these
   framed result stacks with the same work, exact count and parameter.
   There is no new result-shape, nonemptiness or validity assumption.

Terminal iteration is intentionally not duplicated. It is already target 7,
`ActualOriginalParameterizedApplicationResultStackTerminalIteration`, in
the frozen parameterized stack prerequisite. That target fixes the entire
original empty-work live state at every symbolic count and parameter, in
arbitrary context. Its specification is pinned here. Its current proof
work is not assumed accepted and its mutable proof files are not pinned.

## Honest success and padding boundaries

Work append preserves exact final results, not merely live status or
Boolean acceptance. The first run can finish before its stated count.
On appended work, the suffix can then start early. Consequently this
target does not assert that the suffix is untouched after the first
count; a later internal proof must handle terminal padding and return the
same full final stack after the total count.

Unconditional failed-transition result framing is false: an underflowing
finish can fail on a short result stack yet succeed after extra background
results are appended. The result-frame premise therefore remains the
actual successful original run. Its final live empty-work state excludes
absorbing failure internally. No weaker completion predicate or external
execution fact is substituted for that premise.

These restrictions are exactly the original composition packet's
restrictions. Adding a shared parameter does not justify strengthening the
conclusions at intermediate counts or weakening their successful-run
premises.

## Existing proof interfaces and proof boundary

Later proof work can adapt the accepted original composition run/syntax,
state, frame and induction interfaces. Original live/empty-state and list
append graph lemmas are unchanged. The existing arity-generic
`InternalApplicationResultStackReturnSupportProof.returned`, its
`returnedIntro` / `returnedCases`, and the existing `returnedRecover`
remain the return relation for both new callback arities. No replacement
returned relation, decoder, interpreter or assumed callback theorem is
introduced.

The accepted parameterized numeric iteration zero, successor, addition
fusion and fixed-point laws supply internal iterator rules at the same
symbolic parameter. The pending parameterized stack's local lift, wiring,
visit, leaf, finish and empty/terminal graph rules supply transition
interfaces. The original unary composition theorems alone do not prove
this packet for arbitrary parameterized callbacks. The separate external
transition calibration also does not imply these internal derivations.
Any accepted proof must thread the parameter through actual program graphs
and internal induction, not appeal to evaluation extensionality or
standard-model truth-to-derivability reflection.

## Freeze and validation

`FROZEN-SOURCE-PINS.json` pins the three new Lean specification files and
this correspondence. `SOURCE-PINS.json` records the stable local import
closure and selected accepted supplier roots, plus original paper,
configuration and accepted-supplier evidence. Of the currently active
parameterized stack component, only its Definitions, Targets and
Preflight Lean files are included. No mutable stack proof, log, status,
acceptance receipt or ongoing compiler output is frozen as a supplier.

`STATIC-CHECKS.json` reports noncompiler delimiter, source-shape, exact
zero/append/frame formula, alias coverage, import, forbidden-token and hash
checks. Static success is not Lean elaboration, a proof, or an axiom audit.
No proof files were created, no compiler slot was requested or held, and
no compiler command was run. The parameterized stack worker retains sole
native compiler admission. Independent review and the new comparator-only
preflight are pending.

Any later compiler use requires explicit serialized admission and
`scripts/check.py` with unchanged 2048 MiB heap, 1536 MiB process-tree RSS,
2048 MiB minimum free memory, one thread, 90 CPU seconds and 180 wall
seconds, without rebuilding upstream dependencies. The hard cutoff is
2026-11-08 18:00 UTC. Only `propext`, `Classical.choice` and `Quot.sound`
are admissible theorem axioms.

## Excluded claims

No full fold equation, full-run success or output-shape theorem, fixed-fuel
sufficiency, recursive representative fold, canonical selection,
representative congruence/identification, uniform path correctness,
unconditional `CertifiedApplicationLift`, constructor/lambda/substitution
closure, all-term accessibility, or completed paper06 `lem:id1` is claimed.
No original source or target is modified, no global register or
dependency/CI/resource policy is changed, and no Git, publication,
full-root build or remote CI action is taken.
