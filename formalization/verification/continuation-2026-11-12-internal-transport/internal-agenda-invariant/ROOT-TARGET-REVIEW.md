# Independent operational root-target review

Reviewed `OriginalHereditarySourceRootCompletionTargets.ActualSourceRootCompletion`.
Target source SHA-256 at review: `fc11b7ec80beb55019868a4de6aaa863ee96d4abc136db0df73fd1437443e25d`.

The inputs are literal packed/parameter/job/initial-state coordinates, actual
source acceptance, actual branching and fuel observations, and an actual
numeric `RuntimeIteration.run` graph. No `Job`, `Agenda`, potential estimate,
`StepLaw`, empty-work conclusion, native typing, or result-correctness theorem
is an input to this root target.

The intermediate completion theorem does use an internally quantified agenda
and potential entry formula, but the root proof constructs those obligations.
`ActualCompletion` instantiates the staged conditional induction with the
concrete `actualStep` theorem. The entry formula retains the actual arbitrary
result stack and does not presuppose semantic correctness of its contents.

The conclusion `Empty output` is exactly the actual first-coordinate graph
`left(output)=0`. This is operational exhaustion of work. It does not assert a
nonempty final result stack, the provenance of its head as the final root
return, equality to the intended recursive observation, or final source
computability/representative coherence. Those remain separate obligations.

This note is a target/premise review, not a replacement for bounded compilation
or the repository's exact-target verification receipts.

A further deliberate loss of information is that the operational `Frame`
predicate retains literal return counts but not their calibration against the
parent's expansion, nor the completed result-segment partition. The actual
visit constructor computes the right counts, but this invariant need not retain
that fact to prove work exhaustion. A later semantic frame invariant must retain
or recover those relationships in addition to child/deletion contents and root
return provenance.
