# Paper 16: chosen direct checker constituent cut (source freeze)

**Scope.** Pending serial native gate. No claim of whole-checker equality, numeric
completeness, semantic direct closure, or selected-family substitution. Own new
source lives in `LogicLineages/PersistentMarking/NumberedWindowInternalDirectCore{Targets,CutProof,EnvelopeProof}.lean`.

* Paper 16 `16-persistent-marking-termination-ordering/sections/ordinals.tex:74–105`
  (SHA-256 `526aa249902b4e4bf00f45bee770bdcdc9f9b39c2dc341778834600b7f8bf1b5`)
  and `NumberedWindowDirectAlgorithm.lean:12–38`
  (`781ec264d98428a9068e59190f5fbac631bc3bc46470c024f13bf05b206e6e33`)
  specify the literal tag 5 witness order, the tag 4 inserted row order, two
  ordered-list partitions tested by multiplicity/permutation, nonempty removal,
  actual scalar typing of the endpoints, and the retained insertion witnesses.
* Chosen `dCore` is a new conjunction AST, not the old opaque installed `d`:
  `[source,certificate,target]` passes the accepted physical `guardAt 5`
  (#1482) and the actual ordered `field 0,1,2` read on that same certificate.
  Source and target are literal endpoint projections. The five-cell raw core
  tape is `[source,target,kept,removed,inserted]`.
* The original components on that five-cell tape are
  `boundaryRaw scalar [source,target,removed]` (#1507–1510),
  `rawSourceCheck (observePartition count) [source,kept,removed]` (#1501–1503),
  `rawTargetCheck count [target,kept,inserted]` (#1506), and
  `scan positive [inserted,removed]` (#1495/#1500). The two partitions take
  one identical `count : Program 2` parameter, never distinct tests, duplicate
  deletion, or set membership as replacement for counts. Only projection
  composition routes the sub-tapes. The independent scan uses the earlier paid
  original parser, actual ordered rows, and same raw removed tape.
* Cut first gate: actual successful core graph on the five-cell tape recovers
  the four genuine component acceptance graphs via original conjunction and
  projection recovery. Envelope gate: one actual successful `dCore` graph
  object-eliminates its own composition; no supplied field reports. Original
  projection functionality pins source/target witnesses to the literal inputs.
  In the resulting object context, the same chosen kept/removed/inserted form
  the actual ordered field reports, exact tag-5 packed equality (#1482), and all
  four accepted subgraphs. No independent field callback or witness pool.
* `count` is intentionally uninterpreted at these two cuts. Installing the
  original `Continuation20261114.ArgumentCountComparison.permutation` and
  using its numerical/native and all-needle open theorem remain separate; the
  nominal closure still hits unavailable pinned Hydra/GameAdd/Sym2. The present
  cuts do not yet align independent decoded scratch witnesses or extract all
  symbolic insertion member reports at the same cut; they expose the exact
  component graphs to which those independent checked consumers apply.

New SHA-256 pins and source import-scan counts (not artifact receipts):

| Leaf | SHA-256 | Local closure |
| --- | --- | --- |
| `CoreTargets` | `85c38d6a1d033afe6a99797b751e92f03b5ea7164fad1411c4c9e10bdead6638` | 1104 |
| `CoreCutProof` | `756b917b5292abd1ebd6d736f66545d8029f503785ade9668bf16b45484f1a50` | 1107 |
| `CoreEnvelopeProof` | `c167574f5e344e77091b058b862cc33f6656616c67daf9cf5d9e767a3cffbe81` | 1231 |

Each source scan has 32 external imports, with none of Hydra, GameAdd, Sym2
or Linarith in the source-recursive closure. Gate exact aliases:
`NumberedWindowInternalDirectCoreCutProof.exact_OpenCoreCut` then
`NumberedWindowInternalDirectCoreEnvelopeProof.exact_OpenDCore`.

Unchanged component source pins (same PersistentMarking prefix):

| Leaf | SHA-256 |
| --- | --- |
| `WitnessEnvelopeOpenProof` | `96d87ee4812dd7e33383f8dab6f777145a6404404854f573997db6cc854b1955` |
| `BoundaryGuardsTargets` | `88049146da1311327ee3ab56eb9d8c70df332319c2bba8af1cad6d4dd0190725` |
| `SourcePartitionRawTargets` | `132aa95648e74180aa6507215169ccd6e916f3dd0d352c69d6c09983f2c9fc85` |
| `SourcePartitionRawGraphProof` | `42ef4c0c527ce2ca12d02a31450242bb1db87e9044627a764ed25c92605cab0e` |
| `TargetPartitionRawTargets` | `cb0741ecfbba9a74cfc08871b1394f9cacfac1bb1077dd1cdfd0bc9249127cf2` |
| `InsertedScanTargets` | `5e376df2e67a2c3f1417fb552e4cd54290b4db45e549c7db92581b8c77106d4f` |
