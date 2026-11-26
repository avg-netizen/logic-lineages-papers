# Paper 16: source-exact narrow open own-cover proof route

Status: alternative source candidate; native and axiom checks pending.
Original candidate and proof suppliers are preserved unchanged.

The original `FactoredAuxOwnCoverTargets` and `FactoredAuxOwnCoverProgramProof`
are imported without modification. Both final aliases have the literal same
target types and same body as the first edition, apart from the namespace and
replacement supplier. The physical grammar, option and scratch programs do
not change. The source/claim scope remains that of
[P16-FACTORED-AUX-OWN-COVER-SOURCE-MAP.md](P16-FACTORED-AUX-OWN-COVER-SOURCE-MAP.md).

Five thin suppliers retain only the previous open derivation segments:
Cartesian fold cons step and list induction, four-axis auxiliary membership,
and grammar stage step and successor occurrence. The only substantive proof
replacement is two one-sided and one right-sided applications of original
physical append membership, now using `ScratchAppendOpenChecks.fromLeft` and
`.fromRight` instead of the broader original-primary expansion/edge-inclusion
proof imports. The thin root does not import the earlier numerical checks,
the affected primary theory, or explicit Hydra/Linarith. Its static local
closure is 1,364 modules instead of the first edition's 2,392.

| Module suffix | SHA-256 |
| --- | --- |
| `NumberedWindowInternalCoverCartesianFoldThinStepProof` | `0b62f51c4e1117801a136ebb538c25be8801a31d9158ba584bf325d2e0695158` |
| `NumberedWindowInternalCoverCartesianFoldThinOpenProof` | `e87bbfc7de09d277ae9da5c0b6d8b700e3767f22adc990c6c70be9f3fba17a51` |
| `NumberedWindowInternalCoverAuxApplicationsThinOpenProof` | `0741c93342ea031228cdbae01be4629fc8d93aee6ce5b9672956fa06c85c4224` |
| `NumberedWindowInternalCoverGrammarStageThinStepProof` | `3dc60124100f590deb62f075f04c852c3fa8d232209c20137f81bfd3d9059bbf` |
| `NumberedWindowInternalCoverGrammarStageThinOpenProof` | `1f200e518fa00606ac42049df689e46b58cf77689b242ba297fd4ab8dfa87ecb` |
| `NumberedWindowInternalFactoredAuxOwnCoverThinChecks` | `a6b5509b030a7fc4a8197c6462bcd074ddaecea9d26cae37f5f82205e9706f1f` |
