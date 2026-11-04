# Original multiset-certificate presentation and numeric codec

This component supplies effectivity for the unchanged `packedListNumber`,
`decodePackedList`, `certificateNumber` and `decodeCertificate` definitions in
`NumberedMultisetNumericDefinitions.lean`. Those functions encode and parse the
actual `MultisetCertificate` used by the existing Mul checker. Its fields retain
the ordered kept, removed and inserted occurrence lists and the complete list of
literal removed-index/mark-label pairs. The product equivalence changes only the
computability presentation, not the certificate or any Boolean test.

The targets quantify over each fixed finite signature size, arity function and
binder context. Every certificate, list and natural code is an input to the
corresponding primitive-recursive function. Decoding uses the original numeric
list parser and genuine typed packed decoder, including rejection of malformed
codes. No well-formedness premise is added to any target. Existing numeric
round-trip and soundness theorems remain unchanged.

This is a supporting component for paper06's effective quotient reduction. It
does not prove the multiset checker, Copy, the complete root or contextual
checker, a uniform varying-context presentation, arithmetic representability,
ID1 accessibility or a numbered source theorem.
