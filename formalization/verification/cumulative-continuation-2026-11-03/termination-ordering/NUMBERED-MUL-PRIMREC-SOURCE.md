# Original typed and numeric Mul certificate effectivity

Paper06, lines 537–556, specifies the all-Mul auxiliary reduction and the
arithmetic one-step relation. The targets here concern the unchanged
`NumberedMulCertificate.mulCertificateTest` and
`NumberedNumericMul.numericMulTest`. The source manuscript SHA256 is
`bdafe9f113ec4e3ffc390a5a744ae6337f197ab9a69ddcecd006d5dc08c4a66e`.

The four targets are exact raw-to-typed calibration, primitive recursion of
the raw computation, primitive recursion of the actual typed certificate test,
and primitive recursion of the original numeric test. Signature size, arity
and context are fixed parameters; the symbol/type windows, source, target and
certificate vary jointly. Every natural numeric input and the empty signature
are included, without a window closure or well-formedness premise.

`argumentValues` uses the accepted strict argument-spine extractor followed by
the original packed numeric decoder in the same context. Its calibration gives
the exact ordered `argumentList`, preserving repeated occurrences. The raw
computation requires a positive source label and an ordinary target, with the
original result-type equality, head equivalence and target head window test.
It compares only the source and target base lists through the original
`multisetTest`; source extras remain in the source constructor. The certificate
retains all kept, removed, inserted and indexed witness fields.

The effectivity proof composes proved argument extraction, packed decoding,
head guards, exact permutation/indexed replacement and the genuine certificate
presentation. Packed structural encoding and the unconditional calibration
recover the original typed test. The numeric result uses the original source
`decodeUniverse`, target `decodePackedNumber` and `decodeCertificate`; failure
of any decoder returns false exactly as before. Mul carries no precedence-table
parameter.

Definitions and targets were compiled and frozen before candidate proof
authoring in `ROOT-EFFECTIVITY-FREEZE.json`, using bounded comparator receipt
`1793763176589684697-2`. Their respective SHA256 values are
`0f7ab9c1ed2a7f515fc3b200772ea7072db0403a50ee9623847a0e66c76577f5`
and `a008b86e51983b2e7858d04e6383f6511210ee240754f5c41ed4176ee24a0a72`.
These are supporting effectivity results for the original Mul decisions;
whole-source simulation, arithmetic formulas and internal ID1 accessibility
remain separate obligations.
