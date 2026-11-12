# Read-only feasibility analysis: hereditary class observations

Status: proposal and obstructions only. No Program, tuple, target, or accepted proof is changed. Current paired-observation/full-fold laws do not prove the claims below.

## Why the old key alone is not an established route

Correction after checking the retained observer laws: `OriginalStructuralClassKeyDefinitions.key` is the guarded prior traversal C0. `OriginalLambdaTraversalSelection.ObserverLaws` includes preservation of `OriginalConstructorShape.mark`, whose fields retain the root tag and application domain. Combined with the active-core bridge and the original source/window hypotheses, this rules out the previously suggested OTHER-to-application key collision. That suggested obstruction was incorrect and is withdrawn. The existing observer laws should be reused for root inversion rather than introducing a redundant discriminator. Forward application/lambda recurrence plus actual constructor injectivity may then supply child-key inversion; a complete explicit bridge still needs assembly, but absence of root-tag information is NOT an obstacle.

Moreover the all-position minimum requires equality of erased key/rank at every actual cutoff. Same original K is not a supplied proof of these further tests. Coherence of the earlier kernel minimum does not establish identical candidate rows for the stronger minimum. Full selected-leaf coherence also remains distinct from once-minimum coherence: guards, bounded iteration, and sidecars must be transported at the same tuple.

## Candidate finite hereditary observation

A candidate observation at `(typed packed term, runtime parameter)` would contain:

* its old acyclic key and raw variable rank;
* invariant constructor/type metadata;
* recursively, the observations after each actual in-range context deletion;
* recursively, observations of actual constructor children at their actual contexts, including a lambda body at the extended context.

Deletion at cutoff zero of a lambda body is included, not silently omitted as in a parent-free-variable-only observer. This is the important extra closure beyond a list of arbitrary parent cutoffs.

This is NOT a proposal to replace the numerical old representative by the observation. A fingerprint is not numerically the original least-code representative. If built, it would be an additional equality test around the actual class predicate, with separate all-vector calibration of that predicate. The original old-key evaluator would remain unchanged.

## Native Primary invariance is a real obligation

See `TerminationOrdering/NumberedPrimaryEquivalenceDefinitions.lean`:

* `Primary.ordinary` permits equivalent heads, equal result types, and a permutation of BASE arguments.
* `Primary.numbered` preserves number/result/extras, but permits equivalent heads and permuted BASE arguments.
* `ordinaryArguments`, `numberedBase`, and `numberedExtras` provide recursive argument congruence.
* `lam`, `appFunction`, and `appArgument` preserve their ordered constructor structure. `appArgument` is zero-cost Primary motion, NOT a positive RawStep constructor.

Consequently raw head annotations and ordered BASE child lists are invalid fingerprint fields. A viable native-invariant version needs a canonical typed multiset (with multiplicity) of BASE observations, an invariant head-equivalence class rather than raw head annotation (native zero/succ/cases/recursor share the native class; application ignores its annotations; ranked retains its symbol), and ordered extras/application/lambda children. Numbered headResult must not be added: numbered exchange retains the outer result type but does not require equality of headResult; ordinary exchange does. Canonical head-class construction within the original finite window must be supplied; it is not asserted available by this note.

A possible native proof is induction over Primary plus the hereditary observation measure: old key and rank are class invariant; typed substitution transports Primary through each deletion; constructor inversion supplies matching children, with a permutation at BASE nodes; canonical multiset encoding removes only that permutation. Transitivity must preserve all observation fields. Conversely equality includes the root old key, so original class equality follows only with the existing native representative characterization and original source-domain assumptions. None of this is an internal semantic-reflection step.

All-vector class-test calibration additionally needs the original inactive/malformed fallback unchanged. A typed-only Primary theorem alone is insufficient. Context/window/source closure under actual deletion and child visits must be proved before applying the native class characterization at descendants.

## Finiteness and primitive-recursive implementation

Use structural size as defined in `NumberedPrimaryEquivalenceDefinitions`: variables/bottom have size one, lambda adds one, application adds one plus both children, and ordinary/numbered add one plus argument sizes. A child step strictly decreases this size. A lambda child increases context length by one; other children do not. A deletion decreases context length by one and must be proved not to increase structural size.

Thus lexicographic `(size, context length)` decreases. More concretely along a branch, at most `initialSize-1` child steps occur; at most that many lambda extensions occur; at most `initialContextLength+initialSize-1` deletions occur. Hence `initialContextLength+2*initialSize` is a conservative depth bound. The branch degree is bounded by current context length plus child count, each bounded using initial context length/size. Bounded recursion can therefore implement a finite observation tree without a general well-founded runtime operator. Numeric encoding bounds, sorting, source decoding, and total malformed-state handling still need construction and proofs; lexicographic termination alone is not a finished primitive-recursive implementation.

The typed tree has finitely many children even if numerical codes are large. Bound total node count using a finite branching bound raised to the depth bound, rather than assuming the raw Gödel code decreases under every deletion.

## What internal sufficiency would actually require

Signature equality must expose root metadata, matching ordered child signatures, and equal deletion signatures by genuine program graphs. At BASE multisets it gives a matching permutation, not positional equality. These are internal syntax/codec/sorting obligations independent of calibration.

For application/lambda traversal preservation, one would need internal reconstruction congruence for this full signature. Application deletion uses the same cutoff on both children. Lambda deletion uses successor cutoff on the body; the body's own cutoff-zero deletion remains represented in the hereditary child signature. A separate measure induction must establish this reconstruction, including source and actual-context geometry.

For OTHER, the new predicate would need reflexive/domain/row-coherence proofs, its actual minimum must preserve the complete signature, and that preservation must survive the actual descent iterations and sidecars. This cannot be borrowed from the current single-deletion pipeline without proving the changed tests redundant internally or defining and checking a separately named tuple.

Finally full F equality from signature equality needs an actual selected-leaf coherence theorem and constructor inversion; signature preservation alone does not give equality of two F outputs. The entire route is a substantial new construction, not a cosmetic signature extension or a completed canonical-cancellation proof.
