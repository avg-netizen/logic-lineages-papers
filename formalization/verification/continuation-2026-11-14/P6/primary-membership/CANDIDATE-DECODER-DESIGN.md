# Transparent candidate decoder: exact next design (not authored or checked)

## Source observation

The prior diagnosis that D necessarily requires reconstructing a new structural
encoding was too pessimistic. The EXISTING `Primcodable (Code (Fin n))` instance
(`NumberedCodePresentationProof.codePrimcodable`) uses `codeNumber`; Ty uses
`typeNumber`; product encoding is `Nat.pair`. Thus `Encodable.encode` of a
successful `RawPacked n = Ty × Code (Fin n)` is exactly the original input
packed number, not a different external code.

`NumberedUniformPackedDecodingProof.rawPackedCalibration` identifies the
unchanged raw packed decode with the original typed packed decode followed by
`packedCode`. `NumberedNumericDecodingProof.packedNumericSound` supplies its
original round-trip filter. These prove re-encoding equals the input on success.
The same original `decodedValue` wrapper must be split on context/Object decode;
failed wrapper branches return zero for BOTH targetValue and candidateValue.
No assumption of valid parameters or input may enter this native identity.

## Proposed literal AST and exact targets

Define `candidate T : Program 2` as
`InternalAcceptance.branch T (InternalAcceptance.constantZero 2) (.projection 0)`.
When selecting it, use precisely `T = OriginalTypedDecoder.target H G`.

1. For every n, arity, and vector v, the EXISTING candidateValue equals
   `if targetValue n arity v = 1 then v.get 0 else 0`.
   Retain original context/Object decode, original typed-validity filter,
   malformed/default behavior and arbitrary zero input. Zero is not an Option tag.
2. With only existing native H/G calibration, `CandidateCalibrated n arity
   (candidate (OriginalTypedDecoder.target H G))` holds on ALL vectors.
   Use the accepted actualOriginalTypedTargetLeafCalibration; do not select
   an opaque primitive-recursive witness.
3. Independent internal accepted branch: actual graph2 T 1 input parameter
   gives graph2 (candidate T) input input parameter, and arbitrary-output
   graph is equivalent to equality with that same input.
4. Independent internal rejected branch: actual graph2 T 0 input parameter
   gives graph2 (candidate T) 0 input parameter, and arbitrary-output graph
   is equivalent to equality with zero.

The internal clauses require actual T graphs, never native calibration as a
reflection principle. They use the literal Program branch and projection,
existing branch introduction/elimination, totality/functionality and equality
transport. No new semantics or desired mathematical law is stored in an AST field.

## Integration and remaining obligation

The prior membership class factor can consume this EXACT D, eliminating its
opaque candidate-value supplier in the accepted branch. The SAME original
`classTest T L D` remains all-vector calibrated once L is supplied. Selection
creates a new explicit initial tuple; it does not identify prior existential ASTs.

L remains the genuinely larger problem: actual primary-list enumeration,
structural candidate pools, exchange tests and finite reachability. Internal
root-signature completeness and calibrated E-to-primary compatibility remain
unproved. This design does not establish cancellation, I/C or accessibility.

No Lean definitions, targets or proofs for this next design have been authored.
The existing three-contract membership freeze is unchanged.
