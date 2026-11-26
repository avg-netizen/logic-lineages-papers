# Original raw Object transport: source-first candidate packet

Prepared 11 November 2026. Coordinator review and unchanged bounded preflight
must precede proof authoring. All four contracts are pending. No compiler or
Git command is part of this submission. Stop at 17:30 UTC without auto-resumption.

## Original source correspondence

This supports the weakening/single-variable bottom-erasure bookkeeping in
paper06 lem:id1. The original Object is ContextUniform.objectCode Gamma packed:
Encodable.encode (Gamma, packed), calibrated as Nat.pair (Encodable.encode Gamma)
packed. Its raw payload is the original packedNumber, pairing typeNumber tau
with the literal eight-constructor codeNumber. Neither Code Encodable nor
context typesNumber is substituted for these source encodings.

shiftObjectRaw explicitly constructs pair(consCode(d,left X),
shiftPackedRaw(0,right X)). eraseObjectRaw explicitly constructs
pair(tailCode(left X),erasePackedRaw(headCode(left X),0,right X)).
variableRankObjectRaw applies the already frozen packed rank to right X.
The source list cons is succ(pair(d,Gamma)), and its source head/tail operations
are the two unpair selectors following predecessor. These are the actual
original context constructors/destructors, not new list encodings.

Typed calibration retains actual Encodable Gamma, original source renaming
(prefixWeakening with empty prefix), actual singleSubstitution(bottom sigma),
and NumberedVariableCount.variableCount including bound variable occurrences.
OriginalContextExtensionCalibrationProof.typeEncoding and contextEncoding are
the legitimate native encoding bridge; they are not internal reflection rules.

## Four frozen proposed contracts

1. Native typed Object shift, erasure and rank calibration.
2. Independent internal shift exposure: arbitrary symbolic input, domain and
   output graph recover the SAME input pair, actual cons extension, shifted
   packed payload at cutoff zero and SAME output pair.
3. Independent internal erase exposure: the supplied SAME input pair plus
   actual context-cons witness recover packed erasure at cutoff zero and the
   SAME output pair over the literal tail context. No arbitrary context is
   assumed to be nonempty or decodable as a native context.
4. All-raw Object cancellation, with separate native and internal halves.
   The internal half quantifies over arbitrary positive bodies, variable types,
   logical contexts and symbolic input/domain/output terms. The context cons
   and pair witnesses must be constructed internally, not supplied as extra
   cancellation hypotheses. Raw packed cancellation may use the exact frozen
   OriginalRawSyntaxTransportInternalTargets.ActualRawSyntaxInternalCancellation
   only after its proof supplier is independently accepted; a conditional helper
   alone cannot discharge this contract.

## Explicit exclusions

These Programs only manipulate raw Object bookkeeping. They neither select a
new canonical carrier nor modify the final calibrated tuple. They establish no
cancellation across canonicalization: C_Gamma(E(C_(sigma::Gamma)(S x))) = C_Gamma(x)
is still unpaid. No certificate transport, rank invariance under canonicalization,
I/C transport, original lambda computability, constructors/multisets or full
lem:id1 claim follows. Accepted/frozen inherited sources remain immutable, and
the whole-source numbered register is unchanged.
