# Original application-step peel: exact prerequisite

This is a supporting component toward paper 06, `lem:id1`. The source is
`../06-godel-t-termination-ordering/paper.tex`, lines 537–549 for function-side
application reduction and lines 551–556 for the original least-code quotient
and arithmetic edge interpretation. No numbered statement is promoted.

## Chosen next step

Freeze the actual one-step transition before proving the repeated checker.
The transition consumes the original state

    edgeCode(source, target, certificate)
      = Nat.pair source (Nat.pair target certificate).

Its certificate selector is the original pair of path and replacement/root
payload. It succeeds only when:

1. The original raw path is nonzero and its original list head is exactly 2,
   the unchanged code of `appFunction`.
2. Both packed endpoint payloads have the original application constructor
   tag 2. Their outer result-type tags, application domain tags and complete
   argument payloads agree.
3. Reconstructed function and target-function outer type tags are exactly
   `1 + Nat.pair domain codomain`, and the argument tag is exactly `domain`.
   These are explicit arithmetic equality-test ASTs, not hidden leaf promises.
4. The exact-one original endpoint decoder leaf accepts the reconstructed
   `[domain, codomain, function, targetFunction, argument]` input.

The leaf's separate all-input calibration is fixed by `endpointValue`: decode
domain and codomain by the original `decodeType`; decode the function and
argument by original `decodeUniverse`; decode the target by original
`decodePackedNumber`, without a new universe filter. The decoded types must
be the matching arrow, arrow and domain, and the codomain must belong to S.
This explicitly retains the result-type condition rather than silently
assuming subtype closure.

Success rebuilds the function and target at their original arrow type,
strips one original raw-list path cell, preserves the replacement/root
payload literally, and rebuilds the original edge. Any failed guard returns
the entire input state unchanged. Every node outside the explicitly named
Program5 leaf is a concrete original Program AST composed from existing
pairing/unpairing, list coding, equality and conditional/conjunction nodes.
The leaf is not selected by a new axiom or opaque classical choice here.

## Three exact targets

1. `ActualOriginalTransitionCalibration` separately identifies the guard
   and transition with their direct numeric algorithms on every natural
   state, for every leaf calibrated on all natural inputs. This includes
   malformed codes, rejected certificates and every structural mismatch.
2. `ActualOriginalLiftedTransition` is a full-output equivalence in the
   original `InternalCalculus.Derivation body []`, for every original
   positive body, variable type and symbolic arithmetic term. From the
   actual `edgeCode` and `edgeLift` graphs, the actual decoder-leaf graph at
   output one, and explicit source/target arrow tags and argument domain
   tag, the transition graph at arbitrary output is equivalent to equality
   with the original state. Every raw original certificate is allowed,
   including malformed suffixes. No semantic calibration premise appears.
3. `ActualOriginalRejectedTransition` proves that an actual guard graph at
   zero makes the transition graph equivalent to equality with the input
   state at every output. It does not merely preserve acceptance.

The explicit original outer tags in target 2 are essential: `rawApplication`
discards the input function and argument outer tags. Without those graph
premises the transition could reconstruct different raw numbers, so the
exact full-state inverse would be false. They are real obligations, not
syntactic conveniences to erase later.

## Fixed next-stage AST, not an extra claim

The same definitions freeze the intended normalizer and checker:

    normalizer endpoint state =
      repeatProgram (transition endpoint) (rawPath state) state

    checker endpoint oldChecker source target certificate =
      oldChecker (sourceOf normalized) (targetOf normalized) (stepOf normalized),

where `normalized` is the normalizer applied to the original `edgeCode` of
the three checker inputs. The repetition is the unchanged original raw-list
recursor and ignores list heads; the transition checks the current state's
certificate head. It uses no extra rank, numeric fuel or termination bound.

The eventual internal full-output lifted-checker equivalence is NOT a target
of this small prerequisite. Its structural proof should use the checked
front-cons repetition law and target 2 to identify the repeated lifted state
with repetition on the original path and state. This law can be independent
of the particular old checker because it proves equality of normalized
states, not equivalence between arbitrary opaque calibrated checker ASTs.

Separately, semantic calibration to `numericStepTest` still requires proving
that every successful transition preserves that literal original checker;
the seven checked ApplicationStepGuard identities supply the application
semantics. Failed transitions are identities. Finite repetition then
preserves the old checker without a normalization-completion theorem.
Those semantic facts must never be used as an internal truth-to-derivability
rule. The construction selects a particular normalized checker, not an
internal equivalence theorem for every semantically calibrated opaque one.

## Explicit unpaid obligations

- A concrete Program5 endpoint decoder leaf with its complete all-input
  calibration has not been supplied or proved by this packet.
- The original typed source/target/argument formulas must internally derive
  the actual endpoint-leaf graph and numeric outer-tag graphs needed by
  target 2. Semantic decoder success alone does not discharge them.
- The repeated normalizer's full-output lifted graph equivalence remains
  pending, as do semantic one-step and whole-checker calibration.
- Invariant propagation and source/target least-representative application
  congruence are independent pending requirements for the quotient edge.
- This leaf fixes Gamma and the finite window. Context-uniform integration,
  the `ps[0]` parameter, and outer object/pathValue malformed-input handling
  remain to be proved with the original wrappers.
- CertifiedApplicationLift, the multiset/constructor/lambda/substitution
  arguments and the closed all-term ID1 endpoint are not claimed.

## Validation boundary

At the original freeze, definitions, three target propositions and preflight
preceded all proof authorship. A 1,215-case independent bounded numeric layout
smoke check passed then; it is not theorem or acceptance evidence.

The frozen
preflight passed in local-only native receipt `build-reports/1794123838552076795-5.json`.
Proof authorship then used only the unchanged bounded checker. Candidate 014
passed the exact gate in local-only receipt `build-reports/1794125133790181299-7.json`, including
all three aliases and all three main theorem axiom audits. Every axiom closure
contains only propext, Classical.choice and Quot.sound. All frozen source,
original supplier and paper hashes remain unchanged.

The internal proof first derives concrete field and guard graphs from actual
original pair witnesses. Fifteen finite intermediate values are supplied by
proved original Program totality and eliminated through the original calculus.
No witness survives as a new premise. Graph functionality upgrades the exact
lifted-state value to the frozen equivalence at every output. The rejection
law similarly uses the original zero branch and graph functionality.
The symbolic transition support modules do not import this packet's separate
`InternalApplicationStepPeelEvaluationProof`. Their steps invoke original graph
derivations, not that separate semantic calibration.

The separate evaluation proof uses original pairing/unpairing, list coding,
equality and conditional calibration. Smaller supplier modules and selective
view projection simplification keep symbolic unpair reduction within the
unchanged compiler limits. Three earlier isolated evaluation attempts reached
the CPU cap and are retained, along with other elaboration failures; none is
counted as acceptance. The exact successful source import closure has 1,060 local modules,
including public meta imports, with matching successful native receipt rows. Full receipt-closure peak RSS is 1,176,760 KiB; the
peel checkpoint-only peak is 1,096,856 KiB and final gate peak 1,046,908 KiB.

`ACCEPTANCE.json` and `SOURCE-PINS.json` provide the concise acceptance and
source hashes. Full native receipts, logs, immutable candidate copies and
the closure receipt mapping remain local. No full-root or remote-CI check
is claimed. The portable frozen-source pins preserve the original freeze hashes.
