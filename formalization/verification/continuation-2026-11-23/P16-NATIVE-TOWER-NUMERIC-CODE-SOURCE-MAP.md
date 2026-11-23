# Paper 16: literal application fusion and exact natural codes of the native tower

This supporting result uses the actual all-index native witness family
#1472, whose source is the printed sequence (D) in `ordinals.tex:563–572`
and the literal native (t_n) at :584–591. The natural codec is this
repository's fixed literal arithmetic syntax codec, not a numbering
asserted by the manuscript and not the least-code address of a primary
equivalence class.

1. `ordinaryAppRead` preserves the real nominal application head, ordered
   two-child list, domain and result annotations under original `tr`.
   The result uses ordinary tag 4, *not* original auxiliary application
   tag 6. `applicationCodeLiteral` proves its exact ordered arithmetic
   node: `encodeNode 4 [encodeHead (.app σ τ), pair f (pair a 0 + 1) + 1]`.
   The empty argument-list code is exactly 0. The typed fusion theorem
   identifies this formula with `nativeCode (applyClosed f a)` for the
   actual original operands.
2. `exact_PrintedLowerCode` transports that literal composition through
   the genuine descending `printedLower`, consuming the real (B_{l-1},…,B_0)
   in order, at their actual fields and without a supplied collection of
   coded terms. Its input merely holds the exact `tr`/numeric value of
   the starting head. All actual closed extractor operands really
   translate; no absent read is converted into a successful zero.
3. `exact_PrintedTowerCodeRead` fixes the exact decoded top term at every
   index: genuine translated function and final argument under the
   ordinary application constructor, encoded by the generated numeric
   formula, decoder returns that very term. The result remains typed at
   the original `EmptyContext` and native outer type `o→o` by the checked
   literal translation proof. It has the same `nativeCode` as the checked
   closed tower source. It is positive, so the reader's zero default is
   never reached on these witnesses. No closedness or typedness of
   malformed numbers is asserted.

The prior `NativeSyntaxCountabilityProof` uses generic roundtrip/injectivity
and does not compute the composed value at these constructors. This
packet proves a literal syntactic code equation, not primitive recursion,
quantitative code size, ordinal rank, or calibration. Native stages:
`LogicLineages.PersistentMarking.NativeTowerNumericCodeApplicationProof`
(3 named reports) and `LogicLineages.PersistentMarking.NativeTowerNumericCodeProof`
(3 additional named reports).
