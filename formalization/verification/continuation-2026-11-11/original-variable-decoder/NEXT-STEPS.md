# Using the checked original variable decoder

Select a suitable explicit initial leaf witness before choosing the final input tuple. Retain the actual outer-context guard and all other source/target branches literally. Prove all-vector calibration against the original `sourceValue` and `targetValue`, including malformed outer-context codes; native calibration alone cannot justify the internal graph law for an arbitrary previously selected opaque program.

The checked interface is `OriginalVariableDecoder.check : Program 3`, inputs `[type,index,EncodableGamma]`, with `OriginalVariableDecoder.graph out type index gamma` for its actual compiler graph. `OriginalVariableDecoderStatementChecks` exports all four frozen contracts. `OriginalVariableDecoderInternalProof` additionally exports hypothesis-level `consZeroValue`, `consZeroElim`, `consSuccessorForward`, and `consSuccessorBackward`.

The cons-successor law retains arbitrary output and an actual `InternalListCodec.consCode` graph. It needs neither an accepting output-one assumption nor membership of the newly added type in a finite window. Combine it with exact variable-tag exposure at the existing final tuple and original raw variable-shift equations. Choose the stronger base witness first, then apply the unchanged final pipeline and retain every existing package property at that same p.

Supporting derivations use the fact that the literal original drop AST is definitionally numeric iteration of the literal original tail AST. Existing internal front-successor and fixed-point induction laws yield dropCons/dropNil. The checker graph transport retains one common residual drop output and reuses the exact head, equality and conditional graphs. The full cons-zero result derives both Boolean output branches from internal trichotomy and equality-test functionality.

These results do not supply full constructor/list decoding, full original source transport, primary representative transport, canonical cancellation or original I/C. Primary equivalence still cannot replace a strict source certificate.
