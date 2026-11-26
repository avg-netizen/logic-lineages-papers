# Original raw syntax transport: frozen candidate packet

Prepared 11 November 2026. No proof candidates, compiler runs, acceptance claims,
register changes, or Git operations are part of this initial submission.
Coordinator review/preflight must precede proof authoring. The public cutoff is
17:30 UTC on 11 November 2026, with no automatic resumption.

## Source and purpose

This supplies original numeric weakening, single-variable bottom erasure, and
all-variable rank as prerequisites for the lambda/substitution paragraph of
paper06 `lem:id1`. It does not establish internal C/I transport, certificate
transport, canonical cancellation, constructor computability, or full lem:id1.

The original syntax is exactly `NumberedAuxiliaryCoding.Code`; raw numbering is
exactly `NumberedLeastCodeRepresentative.codeNumber`. Its eight constructors are:

- var: pair 0 index.
- lambda: pair 1 (pair domain body).
- application: pair 2 (pair domain (pair function argument)).
- bottom: pair 3 resultType.
- ordinary: pair 4 (pair head base).
- numbered: pair 5 (pair label (pair head (pair resultType
  (pair base (pair extraTypes extras))))).
- argumentsNil: pair 6 0.
- argumentsCons: pair 7 (pair elementType (pair head tail)).

The numbered extraTypes field is `typesNumber`; it is metadata, not a traversed
code and not the unrelated Encodable Gamma context representation. Head, label,
result type, domain, extraTypes, and base/extra order remain literal.

## Explicit Programs and total off-domain specification

`shiftRaw : Program 2` takes [cutoff, raw codeNumber].
`eraseRaw : Program 3` takes [erased typeNumber, cutoff, raw codeNumber].
`variableRankRaw : Program 1` takes [raw codeNumber].

Each is a concrete composition of one explicit finite stack-machine AST, with
its mode selected in Lean's finite inductive Mode, rather than through a PR
representability theorem. The transition, finite numeric iterator, exact
2*raw+1 fuel, initialization, and singleton-result output are given directly.
Every visit carries its erased type and cutoff; lambda descent increments only
the cutoff. Ordinary and numbered nodes recurse through their argument trees,
as do argument lists. This is not the existing app/lambda-only traversal.

For every raw natural, tags 1/4 traverse one child and tags 2/5/7 traverse two.
All fields are read with total Nat.unpair. Tags 3/6 and unknown tags are leaves.
A malformed tag-six node with nonzero payload is retained literally by
shift/erase. Unknown tags are also identity leaves; both have rank zero. Tag-zero
is always a variable. Shift preserves indices below the cutoff and increments
all others. Erasure preserves indices below the cutoff, maps equality to literal
bottom(erased type), and decrements strictly larger indices. Rank assigns 1 to
EVERY variable occurrence, including bound occurrences, and sums all children.

Non-one machine status, unknown frame tags, return frames for leaf constructors,
and stack underflows fail at literal zero. Empty work is an identity step.
Output accepts only live empty work and exactly one result; all other states
return zero. This makes cancellation's exact proposed domain ALL raw naturals,
not merely typed source terms. That all-input cancellation remains a theorem
target, not a consequence inferred from native semantics.

Packed wrappers unpair the original packed input, transform ONLY codeNumber,
and pair the result with the SAME original outer type. They do not canonicalize
or change Gamma. Feeding packedNumber or Encodable.encode Code to shiftRaw is
not its source interpretation.

## Independent native and internal obligations

Native targets separately cover all-state transition/structured calibration,
fuel bounds, work decrease, bounded execution, termination, full recurrence,
raw codeNumber calibration, actual typed calibration, and all-raw cancellation.

For typed weakening use the existing
`NumberedAuxiliaryShiftSupportProof.typedShiftCalibration`.
For typed erasure, `prefixErasure` is the existing single-bottom substitution
lifted through the protected binder prefix. The reusable actual substitution
proof is `NumberedAuxiliarySubstitutionSupportProof.typedSubstitutionCalibration`;
its environment base is
`NumberedAuxiliaryBetaSupportProof.singleEnvironmentCalibration`.
At cutoff zero, the target is literally substitution by
`singleSubstitution (.bottom sigma)`.
Rank corresponds to `NumberedVariableCount.variableCount`, which counts bound
occurrences as well as free ones.

Internal targets quantify over arbitrary positive bodies, variable types,
logical contexts, and symbolic arithmetic inputs. They supply totality,
functionality, literal variable branch specifications, all eight constructor
recurrences, public-interface independence of unused parameters, packed
outer-type preservation, and raw cancellation. No native calibration, native
Acc, source typing, C/I, successful canonical run, source-window or externally
provided bound is an internal premise. Internal derivations must be constructed
from original arithmetic graphs, induction, and the actual machine recurrences.

## Deferred source bridge

Future Object wrappers must retain the same final calibrated canonical Program,
the actual Encodable Gamma code, and the same outer contextCode. Certificate
preimage/ranked-forward transport, rank invariance through canonicalization,
scalar-I induction, arrow/application compatibility, and genuine C transport
remain separate pending work. A native accessibility proof does not discharge
any of those internal obligations.
