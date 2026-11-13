# Source-scope audit: conditional argument-rank aggregation

Coordinator reports full exactAggregation and exactAtRaw native gate PASS
1794577307461922100-49, following Binding3 PASS1794577283596619879-35 and
Core2 PASS1794577297760437930-42. All current mathematical files are immutable.
This is a source-scope review of my own packet, not an independent compiler run.

## Exact boundary

The public aggregation consumes the original ArgumentsAccepted H M W predicate,
actual original parameter pair, actual argumentObservations Q graph and actual
variableRankRaw graph. Q is an arbitrary binary Program and F is an arbitrary
parameterized weighting Program. The conclusion is the literal weighted F fold
on that SAME supplied observation row, at the SAME supplied raw rank.

AllSmall and LocalWeights are explicit internal formulas, not external lists of
facts. AllSmall bounds the E component of every actually looked-up typed entry
at every index below an actual row length. LocalWeights says an admitted actual
head term, actual packed head, actual Q observation, actual typed observation,
actual head raw rank and the strict child bound imply the corresponding F graph.
The final calibration must discharge both conditions. This packet does not
establish global decoder-rank calibration or assume it implicitly. The actual
parameter pair is retained in the public signature but unnecessary for this
pure aggregation; no target was weakened or rewritten.

## Proof route

The induction predicate universally quantifies original spine type, actual
observation row and raw rank inside the arithmetic calculus. Original strong
induction is on the raw spine code. Context.SpineCases eliminates original
admission into literal nil or cons constructors, obtaining original head
TermAccepted, tail ArgumentsAccepted and strict raw-tail descent. The proof
uses no external natural-number induction, evaluated native values, semantic
membership or reconstructed list.

Nil uses original observation nil evaluation and raw-rank nil evaluation,
functionality and graph equality transport. Cons queries six actual Program
outputs by totality, recovers the original argumentObservations cons graph,
and derives head smallness and AllSmall for the actual mapped tail using the
original length and lookup-cons laws. LocalWeights pays only the head graph;
the smaller-raw induction pays the tail fold. Original raw rankSum and weighted
cons recurrence then produce the supplied whole rank. The strong-induction
hypothesis is discharged in rawInduction, not exposed as an endpoint premise.
No sorted-row premise or final weighting/calibration equation is hidden.

No concrete scope defect found in this review. Full canonical Object equality,
source-rank calibration, paper06 I/C, and paper12 HB are not conclusions here.

## Accepted source snapshot

```text
39585a178e08f8af445bf97819c8670c9af47f5fe5c3b3d636525239267b2c10  RankArgumentConsProof.lean
1cf6b672bb192ffdcc48f272892b17f5f3ed0194303d4bba2b19897c28cdcb7c  RankArgumentCoreProof.lean
41da383203920c8385d33efe78bb4a3715f6caa5855e3d9d911035babc9bab61  RankArgumentDefinitions.lean
1b025838afaeca0113900497db5dd12c338863ca6bea48fffe2486b4fa4c5c67  RankArgumentInductionBinding.lean
72d88aa692ada0d5140a96af744492d0cee3886f55a2e7ccb749f5c299cc2a1c  RankArgumentInductionDefinitions.lean
777c1cb3acc4e8a4b985ca12ed98246543974fc71b5571b72b24d78efc7293b2  RankArgumentInductionPreflight.lean
3a932616dd38f223c6ecd396ef5ca720f2962a760e4da05d1b4daa0575bb7317  RankArgumentInductionSyntax.lean
dc55c21eeea781887ffcfc73406107b1a79adfa7ef84b79ba78474e5e0314582  RankArgumentInductionTargets.lean
de8bf1031f91afefde8df913a59754ae4f056604f2cca6ef843d4350f84b20e5  RankArgumentLocalProof.lean
0663110a13ddfeaa358663988ed586c16e8b1f22e0c9a846bf203dcedc43dd12  RankArgumentNilProof.lean
5abb2526e2abf2d95f57bbecaea256331a04c474601d07eeb553d92a97dceac1  RankArgumentPreflight.lean
b7a4c515dc4f17bc15a761d9ce6b2a83024187242da2c5f93c989d5252902f7f  RankArgumentProof.lean
00afe4fc9d501ad6f50a014438927bac398f20f28c61a19235eccfa94fb59518  RankArgumentQueries.lean
15ece192eb7868298e1ff4b341599fc1b8ccbf43fb891052ae297e9fc4959210  RankArgumentSmallProof.lean
6c348549101098622cc8f2e3f8db5051d6dfed93b1ce13b8a5aee0b0812fe0e0  RankArgumentStatementChecks.lean
87c7056a9dc12bd6d0483f58d792056b1ad5bd23c41df9c3617bb05702da8e1a  RankArgumentSyntax.lean
e2f1fbe4b3b7de42b0bbc5710be1aa4e7038e85866ceae76035283aacc4d5525  RankArgumentTargets.lean
```
