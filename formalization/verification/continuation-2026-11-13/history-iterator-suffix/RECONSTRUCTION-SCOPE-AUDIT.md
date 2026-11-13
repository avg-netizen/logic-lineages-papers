# Independent source-scope audit: internal reconstruction

Coordinator reports SurjectivityProof and ReconstructionProof native gates
passed. This audit is source-only; I ran no compiler. Full iterator suffix and
same-source packaging remain pending at this snapshot.

## Pair surjectivity is internal

Targets.InternalPairSurjective quantifies arbitrary installed Program, actual
pair node address, context, and internal code term. Its conclusion is an
internal two-existential pair-image formula in the original PR-defining-equation
PA theory. It does not assume an external State codec or a native code witness.

WitnessProof builds the two existential introductions/eliminations with checked
substitution/lifting. Zero uses the actual registered pair(0,0)=0 equation.
ShellSuccessorProof derives each successor image from literal square-shell
pair equations: lower interior (a+1,b), lower boundary (a+1,0), upper interior
(a,b+1), and upper boundary (0,a+1). Internal exhaustive lower/upper and
boundary/interior splits cover all pairs. SurjectivityProof then invokes the
original PA induction schema on the pair-image existential formula, eliminates
both witnesses internally, and instantiates the resulting universal theorem at
the arbitrary supplied code. No Lean Nat induction or native codec reflection
is used to obtain the arithmetic theorem.

## Decoder and positive-list reconstruction

Targets.InternalDecoderReconstruction has only installed literal pair and left/
right decoder node identities. ReconstructionProof internally obtains a pair
image from surjectivity, applies actual decoderCrossPair inverses and equality
congruence, and eliminates the two existential witnesses. decoderCrossPair
explicitly proves equality between the caller-selected pair copy and each
decoder's embedded pair copy before applying the internal inverse theorem;
addresses are not silently identified.

InternalListReconstruction applies to every arbitrary successor term code+1,
not only a caller-supplied cons image or externally encoded list. It resolves
the cons pair child at ctag + argumentTag, resolves decoder function children
at htag+1 and ttag+1, derives predecessor(code+1)=code at actual predecessor
child addresses, and combines arbitrary-code decoder reconstruction with the
literal cons=successor(pair) defining equation. Zero is intentionally excluded
from this destructor reconstruction, matching the actual nil code.

No concrete premise/quantifier defect found. These results establish local
internal reconstruction, not iterator successful-prefix transport, full raw
State execution, HB2/HB3, or final checker certificate closure. The larger
SameSourceIteratorSuffix target is not paid merely by these helpers.

## Reviewed source snapshot

```text
ecec46c29aced4b2edf4942ed3797f3586a878c9e7ee357d1a757ba091de7296  Targets.lean
9e49b82be09a8ac809e41aa4f75d8effe5b7719d3a11b95b7125c2601a84fb89  Definitions.lean
5c9f38fb2680636f29c5efe731de28e8c9fe87dee54c44ce29b547bfaf21f633  WitnessProof.lean
94f6b3463c5fdd86230c706e3f445e535d32fdb7b97b08d5c4547b6dfb65b12f  ShellSuccessorProof.lean
0db0cf8d65fcdaa59b848b2d6c68e563bfb7124fa60f73637bf785a2979c8328  SectorSplitProof.lean
447328af3d66ab81cb15376b32a65a1b5c5990c823f155b75c4fdb57e9644b59  ImageSuccessorProof.lean
63f9f6ae9e8b9e3ec8fe03acf4b63f7aa66764f2da19e1a172f1f8acdf075f0b  SurjectivityProof.lean
3aa4cf107ee076911438fe8e02b4c4d73faa37dd1fd34879721786b52a268fa7  ReconstructionProof.lean
```
