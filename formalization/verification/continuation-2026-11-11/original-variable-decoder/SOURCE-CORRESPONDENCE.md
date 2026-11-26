# Original variable decoder realization

Frozen before candidate proofs, 11 November 2026. Preflight passed `1794400424071123409-5`; all four exact contracts passed final gate `1794400828639315858-5`.

Paper06 `06-godel-t-termination-ordering/paper.tex`, lines 537–558 fixes the finite subtype-closed window, de Bruijn binders, computable numbering and original least-code carrier. Lines 558–599 (`lem:id1`) require typedness, variable computability and fresh-variable/context extension. This packet supplies only the explicit arithmetic realization of the original variable-decoder component needed by that programme; it does not prove the whole lemma.

The direct mathematical source is `NumberedAuxiliaryDecodingDefinitions.decodeVariable`: nil rejects; zero checks equality of the requested type with the first context type; successor recurses down the context. `NumberedVariableDecoderPrimrecProof.variableSuccessCalibration` is an existing native characterization, not an internal reflection rule.

The fixed AST uses the already accepted original `InternalRawListRecursion.drop`, `InternalListCodec.headCode`, `InternalEqualityTest.equalityTest` and `InternalAcceptance.branch`. Branch order is control, zero branch, nonzero branch. The nonempty check prevents empty-context/ground-type false acceptance. Gamma is encoded by its actual `Encodable` list instance. `typeNumber` is the original Ty code. No `typesNumber Gamma` substitution is made.

Four exact contracts are frozen: original dependent-decoder native calibration; independent internal nil rejection at every output; independent internal cons-zero full Boolean graph; independent internal cons-successor graph equivalence at every output. The last is exact context-extension weakening with arbitrary added type code and no window premise. All internal statements quantify over raw symbolic terms and have no evaluation/correctness/reflection hypotheses.

This is not transport for an arbitrary opaque calibrated leaf. No existing selected input p, global Package or SAME finalData pipeline is changed. Full term decoding, original source/primary representative transport, canonical internal cancellation and I/C remain pending. Accepted/frozen mathematical files, manuscript, checker and limits remain unchanged. Coordinator owns all serialized compiler checks and Git.
