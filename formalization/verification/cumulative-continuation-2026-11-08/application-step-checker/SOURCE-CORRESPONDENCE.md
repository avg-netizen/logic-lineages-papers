# Normalized original application-step checker: exact accepted component

This is a supporting component toward paper 06, `lem:id1`. The source is
`../06-godel-t-termination-ordering/paper.tex`, lines 537–549 for the original
numbered reduction and function-side application rule, and lines 551–556 for
the least-code quotient and arithmetic edge interpretation. No numbered
source statement is promoted.

## Existing concrete checker, unchanged

The targets use the already frozen `InternalApplicationStepPeel.checker`.
No alternate checker, encoding, decoder, state, or calculus is introduced.
Its original three inputs are source, target and step certificate. It packs
those inputs with the original `edgeCode`, repeats the original guarded
peeling transition once per cell of the original raw certificate path, then
applies the supplied old checker to all three original selectors of the
resulting state. The original replacement/root payload is retained.
The repetition uses the original raw-list recursor without rank or fuel.

The preceding peel packet fixes the complete arithmetic transition AST and
its exact original decoder leaf. The leaf decodes the function and argument
with `decodeUniverse`, but the target with `decodePackedNumber`, without a
new target-universe restriction. The domain and codomain use `decodeType`.
Matching decoded arrow/domain types and membership of the codomain in S are
explicit leaf tests. Structural and numeric outer-tag guards are separate
arithmetic nodes. Failure of any transition guard preserves the entire state.
The peel packet is a prerequisite, not a proof supplied by this packet.

## Two exact targets

### All-input external calibration

`ActualOriginalCheckerCalibration` quantifies every original finite signature,
arity map, admitted-symbol list, finite window S, fixed context Gamma and
precedence table. S need not be subtype closed. For every endpoint Program5
calibrated on all natural five-tuples and old Program3 calibrated on all
natural triples, the particular normalized checker has exactly the original
`numericStepTest` Boolean-to-natural output on every natural triple.

This retains malformed source and target codes, malformed position paths,
rejected certificates, structural mismatches and off-window inputs. It does
not condition the equality on accepted inputs, valid certificates or
successful decoding. `StepCalibrated` names only the original old-checker
calibration, not the desired normalized-checker conclusion.

The semantic proof shows that a successful transition preserves the literal
original numeric checker using the checked ApplicationStepGuard identities
and the original pair/list reconstruction equations. Rejected transitions
are identities. Repetition preserves the original checker regardless of whether
normalization reaches a terminal state. There is no new completion premise.
These semantic arguments do not establish any internal derivation.

### Full-output internal lifted-checker equivalence

`ActualOriginalLiftedChecker` lives in the unchanged
`InternalCalculus.Derivation body []`, for every original positive body,
variable type and symbolic arithmetic term. It applies to every old Program3
and endpoint Program5, without semantic calibration assumptions. Its output
is an arbitrary symbolic term, not the acceptance numeral alone.

The premises are exactly the actual original graph witnesses for:

1. The arrow code obtained by original `consCode` from the supplied domain
   and codomain codes.
2. Original `InternalUnpair.left` extracting that same arrow code from the
   source and target, and the domain code from the argument.
3. The endpoint leaf returning one on those same domain, codomain, source,
   target and argument terms.
4. Original `application` producing the two lifted endpoints with that same
   argument, and original `stepLift` producing the lifted certificate.

The conclusion equates the full graph of the SAME normalized checker on
those lifted endpoints/certificate with its graph on the original endpoints
and certificate. It does not equate arbitrary semantically calibrated
programs, assume the normalized states are equal, assume checker invariance,
or add the desired conclusion as a premise. All original certificates are
in scope, including malformed raw suffixes.

The explicit outer tags are necessary because original `rawApplication`
discards the input function and argument outer tags. Without them the
peeling transition could reconstruct different raw numbers. The actual
endpoint-leaf graph is also indispensable; semantic typed-decoder success
is not an internal derivation of it.

The internal route is structural: the original constructor graphs identify
the lifted state and its prefixed path; the lifted-transition rule identifies
its first transition result with the original state; the checked front-cons
raw-list repetition law gives the same repeated state. Original graph
composition then applies the same old checker at all outputs. This does not
need a semantic truth-to-derivability rule or a new arithmetic axiom.

## Explicit remaining obligations

- A concrete endpoint Program5 with its complete all-input calibration is
  not supplied or proved by these two targets.
- Original typed source, target and argument formulas still must internally
  derive the actual leaf and numeric outer-tag graph premises. Those
  obligations remain visible and are not discharged by this packet.
- Invariant propagation and original source/target least-representative
  application congruence remain independent requirements for quotient edges.
- Context-uniform integration, the original `ps[0]` context parameter, and
  the outer `pathValue` malformed-object behavior remain to be assembled.
- CertifiedApplicationLift, constructor/multiset/lambda/substitution
  arguments and the closed all-term ID1 theorem are not claimed.

## Freeze and native acceptance

Definitions, the two target propositions and preflight were frozen before
proof authorship. The native preflight passed at those bytes before the
proof authorship began. All three frozen source hashes,
all 31 pinned prerequisites and the original paper hash remain unchanged.
The original freeze receipt is retained locally; the portable
`FROZEN-SOURCE-PINS.json` records those same immutable source hashes.

Both targets now compile at their exact frozen types. Two comparator aliases
and both public theorem axiom closures were checked; each uses only
`propext`, `Classical.choice` and `Quot.sound`. The full 1,094-module local
import closure, including public meta imports, has a successful native
receipt matching every current source hash. `SOURCE-PINS.json` records that
closure. No whole-project or remote-CI build is claimed.

The serialized profile remained 2,048 MiB heap, 1,536 MiB observed RSS,
2,048 MiB minimum free memory, one thread, 90 CPU seconds and 180 wall
seconds per module, using only the existing pinned upstream cache. Peak
successful observed RSS for this packet was 1,029,400 KiB. The maximum
across its full source-matched dependency receipt closure was 1,176,760 KiB.
Ordinary parser and simplifier failures were repaired constructively; all
candidate sources and native receipts remain local. No limit was increased,
existing source altered or target weakened.

The portable publication packet consists of the seven accepted
`InternalApplicationStepChecker` Lean sources and five evidence files:
`FROZEN-SOURCE-PINS.json`, `SOURCE-CORRESPONDENCE.md`, `SOURCE-PINS.json`,
`ACCEPTANCE.json` and `STATUS.md`. Raw receipts, logs, candidate snapshots
and the local closure-receipt mapping are not part of that packet.
