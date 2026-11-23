# Paper 16: actual same selected auxiliary parent window (source freeze)

Gate order:
1. `NumberedWindowInternalMeasuredUnrestrictedWindowReportsProof`,
   SHA-256 `93a4a1f0dc666e899d62cfe21a7f4aa73b370b3519579202ec9aa12c2765d805`.
2. `NumberedWindowInternalMeasuredUnrestrictedAuxiliaryWindowProof`,
   SHA-256 `02b41e49ca95900ab6f174953645d4f3f8e744659636e568913549ed5012dc53`.

The installed W at both actual children and the parent is the same
`window C s (intrinsicQuery (selectedIntrinsic (windowUpdate base T))) (auxSyntax V TV)`.
Function child type is literal `rawCons dom cod`, argument child type is
`dom`, parent type is `cod`, and the parent raw key is the original
`auxiliaryTerm dom cod fn arg`. Both actual type-guard pairs T and TV are
held independently at `dom` and `cod`, with no numeric-to-object transfer.

The reports root peels the actual conjunctions and raw projection, or
rebuilds the literal syntax-window conjunction with its exact positive
V graph. Its context CPS opens the actual successful contextOption from
the function child's held contextPresent positive; zero would force an
impossible zero-constant unit. Even a nil context payload is legal. The
aggregate retains that exact slot-0 raw context and moves the original
physical parser output, not a decoded replacement context, to the
parent via `exact_OpenUnrestrictedContextOptionMove`.

The unchanged intrinsic base program uses `exact_OpenAuxWindow` of the
passed thin recut. The unchanged selected syntax `auxSyntax V TV` uses
`NumberedWindowInternalCoverAuxSyntaxOpenIntroProof.exact_OpenCoverAuxSyntaxIntro`;
the witnesses for both bits come directly from the two held windows.
The aggregate rebuilds the actual syntax window and the actual covered
window using the parent exact cover output and genuine own membership.
C is parametric; the original factored cover is a direct instantiation
with no program substitution. The parent scratch and membership are
explicit premises on the same original physical `scratchVertices C s`;
they are not inferred from an opaque window. The result does not claim
unconditional own-cover, least selection, exchange or representative equality.

Native acceptance is not asserted in this initial source freeze.
