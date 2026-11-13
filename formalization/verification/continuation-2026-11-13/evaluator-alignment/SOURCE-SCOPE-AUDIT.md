# Independent source-scope audit: evaluator alignment

Full exact3 native gate PASS1794577738718282215-30 reported by coordinator.
All modules present in that receipt match current source SHA256. This audit is
source-only, with no compiler run or changes to accepted mathematics.

## Endpoint boundary

ActualRoot assumes only the original AdmittedPair (both original source checks
and the SAME evaluator relation) and actual independent tag/type selector graphs.
It derives tag equality and packed-type equality. ActualApplication and
ActualLambda assume independently supplied original ApplicationFields or
LambdaFields on both sides; they do not assume common binder or result types.
Application derives domain/codomain equality. Lambda derives those equalities
and equality of the actual independently supplied extended child parameters.
There is no final caller-supplied root tag range, child admission, child-value
equality, evaluator-layer equality, or desired field equality.

## Source route

sameCases queries one actual evaluator output shared by the relation. The
original admitted evaluator-layer theorem recovers the recursive root via the
literal envelope's right-then-left projections. Tag recovery uses the literal
root observer, not a replacement summary. SourceTags unpacks the original
source checker to TermAccepted and reconstructs the raw tag/payload pair;
TermTags excludes tags6/7 and unknown tags using original rejection equations.
Thus the six-constructor disjunction is derived, not supplied.

RootShared queries the common root's tag and dispatches all six actual cases.
The case-specific type proofs extract the literal observer fields and original
source typing; lambda uses the actual arrow encoding rather than conflating
its domain with its packed type. Application/lambda shared-output helpers query
actual payload projections and use graph functionality to identify both sides'
independent domain/codomain selectors with common values.

Lambda's child-parameter equality is separately reconstructed: query the SAME
parent parameter's outer context and gamma, cons the now-proven common domain,
then rebuild both original childParameter pairs and use pair functionality.
No extra G-extension condition is assumed; the original G checks outer context.

The repaired TagRecover/TypeDispatch conversion changes equality conclusions
inside fixed derivation contexts via congrArg, avoiding the earlier failed
context-rewriting draft. Earlier failures remain archived and are not evidence
of acceptance. The final gate verifies the exact frozen endpoints and allowed
axioms; no audit suppression or limit change was used in this packet.

No concrete scope defect found. These are structural consequences of admitted
E equivalence. They do NOT identify E with an arbitrary ObservedPut Accepted
relation, prove final folded output equality, establish Object cancellation,
or close paper06 I/C. The old native OriginalFinalObjectCoherence cancellation
at finalData p is a distinct already-existing theorem, not an internal SAME
ObservedPut or hereditary-evaluator bridge.

## Accepted source snapshot

```text
fe9061220d9cd02c898494de5ad34eb000081dfb02d52d35ab75f783658af3e2  EvaluatorAlignmentArrowProof.lean
7398ed2cdb5da4b5119650aa865e37d216233da8ac85db1ec975489b8852cb46  EvaluatorAlignmentAssemblyProof.lean
29b9f16406dc05d13cd83118717693783896e7537f72cc36afdc6e2dcbb81b0b  EvaluatorAlignmentBranchesProof.lean
ea7d04d6415080a5b07db18d62dffddc59d74df27c17ec27e5f1943890450a76  EvaluatorAlignmentDefinitions.lean
9b3eb3c8b3f093e68407af1aec03469c1bcf114121fd818169a7a6f4599efcea  EvaluatorAlignmentFieldsProof.lean
ab9478d6dc1669de6126d0b3176799eb3951221cae6229b8b34ed14af5cc43eb  EvaluatorAlignmentLambdaProof.lean
ae333ebfdd96f1af59da0d95d1a6359e942920385185c48e5fb290d062df129d  EvaluatorAlignmentParameterProof.lean
e1b1c38eed6e7b271cab6e690de1f7d4b860a5bb089b4f5fc6e8d0a3969cd085  EvaluatorAlignmentPreflight.lean
c14d8326da71d2c7ac3e6a80074d98d1208c5c98b8683667394e40e5d784c107  EvaluatorAlignmentProof.lean
cc3145ee0ec2735afc138ac048d93d86e99508eec780fa5ebba896d14b8b025c  EvaluatorAlignmentRootSharedProof.lean
c455484d44dac5a3331c2368afc7e52cc31803ce9dc3709ea5e137bbf85019be  EvaluatorAlignmentSharedProof.lean
9d25a5e4448e258daeef8c52d952032d65ea4e64800d26fa28609f623db983aa  EvaluatorAlignmentSourceTagsProof.lean
0ba8fc79f3a6c16f64b93085565161e5ce1dede0cbfe186ba87103a8d2e7a19f  EvaluatorAlignmentStatementChecks.lean
a08d6b4007f13176d88995b7150a54de01c0424da822c253d3b6e381a15f1df3  EvaluatorAlignmentTagRecoverProof.lean
ff519a6fb557d8caa47a66c0d67706c0d48492371995b6d68696ac115711d726  EvaluatorAlignmentTargets.lean
fc3949010cd76cc82b7c0e7bf953683e2dc2394c52b75dcf24d47accd29faada  EvaluatorAlignmentTermTagsProof.lean
dbb8d72cde915e3c2f3011548f2a369b2efed5a217ed70a27601c33996995c19  EvaluatorAlignmentTypeDispatchProof.lean
8b14909c073d9435d9fb757070309d9cdcb13dad43e9490e605bd9b518b554d3  EvaluatorAlignmentTypesProof.lean
```
