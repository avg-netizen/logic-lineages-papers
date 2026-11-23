# Paper 16: literal typed raw list program and open parser/scratch cut

Source freeze. The old `NumberedWindowDirectProgramProof.domain` proves
existence by external `unaryCorrespondence` of a closed numerical function;
the old #571 `j` need not expose its parse or checked-list branch.
`NumberedWindowDirectAlgorithm.typedList` (lines 26–29, SHA
`781ec264d98428a9068e59190f5fbac631bc3bc46470c024f13bf05b206e6e33`) and
`NumberedWindowAddressCheckers.multisetDomain` (line 11,
`230df67302d44089dfc20b7c6e3666abdca359a00181d58e0691dd4dbe5197f5`)
specify the exact source-facing typed carrier of Paper 16's odd (A) clause
(`16-persistent-marking-termination-ordering/sections/ordinals.tex:84–98`).

**Literal installed candidate.** `jRaw i` uses the same original unary sparse
list parser. An actual parser output zero takes the constant rejection branch;
a genuine parser successor feeds its exact predecessor payload into the
existing `typedScratch i` proof-relevant code. This is not the nonempty
removed-list guard. Valid packed empty succeeds as actual parse `some []`
(code one), giving scratch nil zero and the vacuously true scalar fold.
Malformed is actual parse `none` (code zero), not accepted as empty. No list
reorder or change to original scalar callback.

**Gates.** The numeral root proves exact `evaluate (jRaw i)` to literal
`typedList scalar` at every raw numeral from sole `ScalarFit`, using the same
exact original parser and #1507. The object root eliminates the actual program
at arbitrary open raw terms by `optionGraphCases`; its survivor is the real
same-key successor parser report and a real selected `typedScratch i=1`
at that exact payload, inside an extended object context. Its converse
reconstructs the acceptance from exactly those same held reports. It proves
neither a transported old-j acceptance nor per-needle typing/permutation
invariance. Reinstalled body off this candidate is a separate packet.

| New module prefix `NumberedWindowInternalDirectTypedList` | SHA-256 | Local / external source closure |
|---|---|---|
| `Targets` | `7674e387aa4670844e7cc7d1b931a8559e090156c0bc50a5a5e798c44dd55956` | 1044 / 30 |
| `NumericProof` | `182fbb59b4cd6ff5d439fd6fb3b27afcd9eb2be572e26873347d104273a2eae3` | 1113 / 32 |
| `OpenProof` | `d07a0327bec12b3d687ff40066df75853c75892ddf6010776011c07c90754a67` | 1095 / 31 |

None of Hydra, GameAdd, Sym2, Linarith appear in recursive source scan.
Gates `NumericProof.exact_NumericJRaw` and
`OpenProof.exact_OpenJRaw` / `OpenProof.exact_IntroJRaw` independently.

Original suppliers: boundary scratch numerical proof
`cc6c867d862eb3a6703e4fee6e34e798986e234dedab12417a04e62d1f022abc`;
boundary target AST
`88049146da1311327ee3ab56eb9d8c70df332319c2bba8af1cad6d4dd0190725`;
sparse original parser numeric checks
`557c0499b52372d7296e1d6030221540c6b08b77387746299efc395a3f25fe3b`;
same actual option graph eliminator
`aa7830497ba1c44bfc7e98508b1a1a40dd684652584411a67a1bcf290df68282`.
