# Bounded application validity: external all-input calibration

This packet continues the accepted application-validity-stack prerequisites
without changing any existing frozen definition or target. It is a supporting
component for paper06 `lem:id1`, not a numbered statement promotion. The source
is `../06-godel-t-termination-ordering/paper.tex`, lines 537–549 (typed auxiliary
syntax, finite windows, application reduction) and 551–556 (type-preserving
quotient). All statements retain fixed n, arity, symbols, S, and Gamma.

## Exact original implementation

The target is the already frozen `InternalApplicationValidityStack.validator`
and `recursiveData`, not a newly chosen extensionally equivalent Program.
The literal recursion repeats the original numeric transition exactly
`payloadValue value + 1` times, beginning at status one and the ORIGINAL
numbersNumber singleton list containing the whole packed input value. The
finished test requires BOTH status one and an empty worklist.

Only tag-two application nodes are opened. Their original payload is
`pair 2 (pair d (pair fp ap))`, and their typed children are
`pair (1 + pair d e) fp` and `pair d ap`. All other nodes delegate their WHOLE
packed value to the old calibrated validity leaf. The source node guard is
the existing all-input membership Program at the result-type code. The target
node guard is constant one and introduces NO universe restriction.

No decode-success, well-typedness, canonical-representative, closed-window,
term-validity, or input-bound hypothesis is introduced. Arbitrary malformed
numeric inputs stay in the all-input evaluation quantifiers. Source is the
original rawCarrierTest (decodeUniverse with universeTest); target is the
original decodePackedNumber.isSome.

## External execution and exact fuel

The only new executable definition is an external State iterator for the
existing stateStep. It mirrors the frozen Program recursion, applying the
transition to the preceding state. It is a specification helper, not a new
validator, primitive-recursive existence oracle, or internal inference rule.
The encoded-iteration target covers every count, original worklist, status,
and arbitrary numeric output of the Program leaves.

Sufficient fuel uses the already checked weight
`sum (payloadValue value + 1)` over pending values. The accepted one-step
bound proves that opening an application decreases this weight, since
`fp + ap + 2 <= pair 2 (pair d (pair fp ap))`. A successful leaf removes
positive weight, and rejecting either test clears the nonempty list. This
strict decrease holds without assuming any input is valid. Reconstructed
arrow type codes may grow, so no packed-code bound may replace the measure.

The sufficient-fuel target proves:

1. Any live state becomes either failedState or live-empty after any count
   at least its original work weight. This includes empty live states and
   zero iterations, and gives EXACTLY the validator's singleton payload+1 fuel.
2. Every arbitrary initial status reaches those same two canonical terminal
   states after work weight plus one steps. The extra step handles a non-one,
   nonzero status whose original list is empty; such a state is not yet the
   canonical failure at count zero.
3. Both canonical terminal states are fixed under every number of transitions,
   for every numeric node and leaf. Thus failures cannot become acceptances,
   and unused extra fuel cannot change a settled result.

This pays numeric termination and sufficient fuel externally. It does NOT
prove any object-language induction, graph equation for fuel, or internal
sufficient-fuel theorem. No termination premise is assumed.

## Exact calibration targets

The component-validator target proves full numeric equality, not merely
acceptance equivalence, for each complete bounded validator on every unary
input vector. It consumes only the original old-data Calibrated predicate
and original MembershipCalibrated predicate. The accepted original validity
invariant, now iterated to a proved terminal state, must connect acceptance
back to the original singleton's validity. Both finished outputs and original
tests are zero or one, so acceptance equivalence gives the exact numeric test.

The final target states the ORIGINAL InternalOriginalStepGuard.Calibrated
predicate for the EXISTING recursiveData old member. In that AST sourceValid
is targetValidator AND universeValidator, while targetValid is targetValidator.
The original source test implies the original target test because
original decodeUniverse filters original decodePackedNumber. This fact must
be proved from the unchanged definitions, rather than supplied as a premise.
The source conjunction therefore returns the exact original source test for
all inputs; it imposes no new source or target universe filter.

## Boundary and remaining work

This packet is entirely semantic. InternalApplicationValidityStack's checked
one-step push and syntactic source-to-target projection remain separate facts.
External calibration never identifies Program graphs and never licenses an
internal derivation from natural-number truth. Internal numeric iteration,
sequencing, sufficient-fuel stability, and complete application-constructor
acceptance remain future obligations. This packet does not consume or claim
the separate internal NumericIteration worker's results.

Representative congruence, complete typed-edge assembly, joint-Gamma wrappers,
outer pathValue malformed-object handling, CertifiedApplicationLift, and the
source multiset/constructor/lambda/fundamental/all-term ID1 endpoints remain
pending. No numbered source statement, full-root build, or remote CI is paid.

## Freeze and verification state

Definitions, Targets, Preflight, and this correspondence are frozen before
proof authorship. Independent review and bounded serialized native preflight
are required before proof writing. No compiler, author, Git action, existing
frozen-source edit, resource increase, or global register edit was performed
by the preparation worker. Acceptance later requires exact-target aliases,
actual standard-axiom audits, and source-matched closure receipts.
