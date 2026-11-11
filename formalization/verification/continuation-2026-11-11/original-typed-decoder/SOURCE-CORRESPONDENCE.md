# Original transparent typed decoder

First packet, 11 November 2026. Definitions and eight exact contracts are
frozen before candidate proofs in FROZEN-SHA256SUMS. Preflight and proof acceptance are pending.
This is a supporting realization of the original decoder, not completion of
paper06 `lem:id1` or the remaining independent internal I/C obligations.

## Original mathematical and algorithmic sources

Paper06 `06-godel-t-termination-ordering/paper.tex`, lines 537–599, fixes the
finite subtype-closed window, de Bruijn contexts, computable numbering,
least-code carrier, and computability obligations. The actual source decoder
is `NumberedAuxiliaryDecoding.decodeTerm` / `decodeArguments`, with the original
raw numbering from `NumberedLeastCodeRepresentative` and decoders from
`NumberedNumericDecoding`. Nothing replaces those source domains or semantics.

The machine implements EXACTLY `NumberedTypedRequests.Request` and `.expand`
and `NumberedTypedEvaluation.evaluate`. Its numeric request representation is
new, literal implementation machinery, not an Encodable Request code:

- term: pair(0, pair(Encodable Gamma, pair(typeNumber tau, raw codeNumber)));
- arguments: pair(1, pair(Encodable Gamma, pair(typesNumber types, raw codeNumber)));
- work: the existing numbersNumber list encoding, nil zero, cons successor(pair);
- state: pair(status, work), with failed state zero and live empty pair(1,0).

The program consumes the first request and prepends its ordered children before
the unchanged work suffix. Original lambda context extension uses the accepted
original list cons. Application processes function before argument. Numbered
nodes process base before extras, retain all extra types and label fields, and
compare the node's declared result with the requested type. They DO NOT compare
the head result with that requested type. Ordinary nodes do compare head result.
Argument nil requires literal tag six with payload zero and empty expected
list; malformed nil, unknown tags, illegal term/list constructor modes and
failed guards reject. Non-one state status rejects. Failure and live empty are
fixed points.

The accepted `OriginalVariableDecoder.check` supplies the exact original
nonempty-context/de Bruijn variable test. Contexts are always Encodable Gamma,
never silently substituted with a raw packed type-list encoding.

The only selected metadata leaf H decodes an unchanged head number and returns
zero on invalid heads, otherwise successor(pair(head result type, ordered head
argument types)). The existing primitive-recursive head decoder, head signature
and type/list encoding suppliers plus allPrimitiveFunctions supply H. Its
opacity is safe only because later transport reuses exactly the same head
input. No complete recursive decoder or oldTarget is left as an opaque leaf.

## Exact frozen contracts

1. One all-vector calibrated H exists for each ranked signature.
2. The literal request codec round-trips the existing Request and reconstructs
   every successfully decoded raw request.
3. Local expansion and every fuel-bounded traversal agree with the existing
   expand/evaluate algorithms, preserving child order and work suffix.
4. All-vector native transition, encoded state, iteration, completion and term/
   argument check correspondence, for arbitrary H.
5. Raw work strictly decreases and raw+1 fuel suffices for singleton requests,
   without typing, head calibration or valid-code premises. Completion may be
   failure or live empty; acceptance is not assumed.
6. All-vector term, argument and packed checks equal the ACTUAL original
   Encodable-Gamma/type/types/code and dependent decoder chain. Accepted raw
   inputs reconstruct an original codeNumber, not merely a typing relation.
7. An independent arithmetic derivation of the full one-step transition graph
   for arbitrary H, with an explicit pair/list/constructor-dispatch formula.
   No native calibration, reflection, run success or graph-alias premise.
8. All-vector equality with the original binary targetValue, retaining the
   mandatory original outer Context decoder G at left(parameter) and the
   explicit term checker at [left(value), right(value), right(parameter)].

Existing source suppliers include NumberedTypedRequestsProof.termExpansion and
argumentsExpansion; NumberedTypedEvaluationProof.anyFuelSound,
sufficientFuelExact, termEvaluation and argumentsEvaluation;
NumberedRequestNumericBoundProof.codeWeightBound; and
NumberedNumericTypedValidationProof.termValidation, argumentsValidation and
packedValidation. The all-raw unary/binary child-number bounds in
OriginalRawSyntaxTransportWeightProof justify raw+1 work rather than the
larger reconstruction budget used by a result-stack fold.

## Deliberate remaining scope

The independent internal bounded run, append/recurrence/termination,
shift/erasure transport, canonical internal cancellation, original source guard
and primary least-code search remain separate obligations. Source guard must
later use NumberedUniverseRequests.guard and its full HeadInWindow condition,
not mere head-result membership. No arbitrary calibrated opaque oldTarget gets
an internal transport theorem from native equality.

This packet does not modify a selected initial p, finalData or the existing
OriginalFinalNativeAccessibility.Properties pipeline. Later integration must
select a concrete initial tuple and retain EXACTLY that existing final pipeline
and its entire Package. All accepted/frozen mathematical sources, manuscript,
toolchain, checker and resource limits remain unchanged. Only the coordinator
runs serialized native checks and Git operations.
