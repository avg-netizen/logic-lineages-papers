# Context-uniform original multiset certificate decoding and checking

Paper06, lines 537–556, uses marked replacements of a nonempty part of the
base list in the all-Mul auxiliary reduction. The immutable implementation is
`NumberedMultisetCertificate.multisetTest`, with the original numeric layout in
`NumberedMultisetNumeric.decodeCertificate`. The manuscript SHA256 is
`bdafe9f113ec4e3ffc390a5a744ae6337f197ab9a69ddcecd006d5dc08c4a66e`.

The four targets calibrate the raw certificate decoder and raw multiset test
to those original operations and establish their primitive recursion. Raw
certificate data is the genuine product of the kept, removed, inserted and
witness lists. Every packed term contributes its actual `packedCode` pair;
the witness list remains unchanged. This product has a fixed presentation
independent of the binder context, including the empty finite signature.

Decoding traverses the original numeric list and certificate layout using the
proved context-uniform packed decoder. Its calibration covers every context
and natural certificate number, preserving failure. Primitive recursion treats
the context and number as joint inputs, using parameter-retaining list folds;
it is not inferred from the earlier results for each fixed context.

The raw marking operation retains the outer type and performs the original
partial marking through all initial lambdas. Injectivity of `packedCode`
calibrates each actual witness equality. The replacement test preserves
ordered inserted occurrences, removed indices, repeated indices, missing or
extra witness rejection and out-of-range failure. Exact list permutations
retain multiplicities; removal must be nonempty and insertion may be empty.

Definitions and targets were compiled and frozen before candidate proof
authoring in `CONTEXTUAL-EFFECTIVITY-FREEZE.json`, comparator receipt
`1793765185672810400-2`. Their respective SHA256 values are
`78ebfc03e6b95209c26d71fa8b7d15db76b0263bff50361f364b2c19b632bc8c`
and `592b788bae5e47ddc6a2d17f3df343b559eb28d12b45196ebc7558720a8e4724`.
This component supplies the context-uniform Mul certificate data needed at a
focused hole; full contextual checking and arithmetic representation have
separate exact targets.
