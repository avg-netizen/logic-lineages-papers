# Paper 16: conditional all-numeral direct-core correspondence (source freeze)

Pending exact serial native gates. These are new leaves extending, and
not modifying, the passed `NumberedWindowInternalDirectCoreTargets.dCore`
(`85c38d6a1d033afe6a99797b751e92f03b5ea7164fad1411c4c9e10bdead6638`).

**Source.** `16-persistent-marking-termination-ordering/sections/ordinals.tex:74–105`
(SHA-256 `526aa249902b4e4bf00f45bee770bdcdc9f9b39c2dc341778834600b7f8bf1b5`),
and literal `NumberedWindowDirectAlgorithm.lean:12–38`
(`781ec264d98428a9068e59190f5fbac631bc3bc46470c024f13bf05b206e6e33`).
The report compares actual evaluation of the chosen three-input AST on
`[src,cert,dst]` with the numeral Boolean of this original `direct`, for
every three naturals, including malformed inputs.

**Exactly three calibration interfaces.** The theorem takes the same
`boundary` `ScalarFit`; `PositiveFit` is evaluation of the unchanged supplied
`r` on the literal tape `[dominator,certificate,target]`; `CountFit` is evaluation
of one unchanged supplied `count` on `[numbersNumber s,numbersNumber t]` for
every actual list pair, equal to the numeral `decide (s.Perm t)`. It does
not assume the entire direct result or the raw source/target partition results.
It does not instantiate the historical permutation program or assume output
semantics on noncanonical scratch tapes.

**Proof seams.**

1. `NumericSupportProof`: exact physical sparse parser acceptance/payload,
   existing actual conjunction evaluation, and numerical calibration of unchanged
   `InternalApplicationValidityStackAppend.append`. The append recut uses the
   same raw fold, same `appendStep`, same existing cons evaluation and same
   ordered append recurrence as `Continuation20261114.PrimaryExpansion.NativeProof`
   lines 79–97, avoiding its unrelated blocked Hydra closure. It is not a
   new substitute append.
2. `NumericPartitionsProof`: source appends actual kept and removed encodings;
   target appends actual kept and actual ordered target projection from
   `exactRawInsertedTargets`. Both feed literally the one `count`. Actual malformed
   sparse input or malformed original tag-4 target extraction rejects, with no
   conversion of nil to malformed or collapse of duplicates.
3. `NumericScanProof`: applies the existing exact insertion scan theorem to
   the actual inserted list and held successful original removed parse. On those
   rows, literal `readEntry`/`entries` gives the same ordered list of actual
   target/dominator/certificate triples. The existential equality test for each
   dominator matches original membership, and same supplied positive calibration
   is on its real ordered tape. A malformed row rejects, not drops. The final
   direct proof independently rejects absent removed parses at the boundary.
4. `NumericProof`: route projections only, same actual selected tag-5 raw
   guard/fields and accepted `exactRawTriple` (#1482), plus #1508 scalar/nonempty
   and the partition/scan results. Reordering conjunction factors uses Boolean
   commutation only; the two partition inputs remain ordered scratch codes and
   the semantic test remains `List.Perm`. No original callback, AST, or source
   manuscript changed.

**Nonclaims.** No original nominal whole-checker identification, no
permutation program installation, no open reflection of all-numeral
calibration, no internal count or saturated direct/J/accessibility result.
The historical nominal dependency remains separately blocked. Open shared
tape assembly is a different lane.

| New leaf prefix `NumberedWindowInternalDirectCore` | Frozen SHA-256 | Source local closure |
| --- | --- | --- |
| `NumericTargets` | `1047be3b919f127c79a59e2cb439abdc3a5fbbed8c9daba99984011ff6dd17f3` | 1105 |
| `NumericSupportProof` | `1be0236d0b531edd9ddd68b1a3210271c4f73e1d536fa05ffe771dc95ab4b0f1` | 1132 |
| `NumericPartitionsProof` | `03be615e873a8ddcc6af96f5eb2bbdb1ce8a0bdc5bbfb94e30bf4da85aadfdcf` | 1141 |
| `NumericScanProof` | `e845de8db11ef15c21738223130cfc50608d3c53a0f17449d8f814d86d6a7455` | 1144 |
| `NumericProof` | `982991fd53d218677732be0c4c6d20ddcfd2090c1dc8c1e3ef611605154f0ddb` | 1151 |

Each source scan has 32 external imports; no Hydra, GameAdd, Sym2 or
Linarith listed in the recursive source closure. Gate
`NumericPartitionsProof` (includes `NumericSupportProof.appendValue`),
`NumericScanProof`, and `NumericProof` independently before any promotion.
Exact aliases: `exact_NumericSourceObserver`, `exact_NumericTargetObserver`,
`exact_NumericInsertionObserver`, `exact_NumericDCore`.
