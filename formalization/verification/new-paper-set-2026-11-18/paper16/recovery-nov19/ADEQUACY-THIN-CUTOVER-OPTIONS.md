# Adequacy cutover options (offline design, not an authorization or result)

Original owner-side `ProtectedSpineStrictMarkProof` was source-matching
but exceeded the cloud core RSS cap. A new proof of the identical
`MarkingFields` proposition is drafted separately. Do not redirect anything
until the new supplier independently passes and is reviewed. Preserve the
old proof bytes, receipt and all frozen/accepted and pending owner evidence.

The downstream source-use audit for a possible append-only cutover:

| Affected original source | Exact use of old strict-mark proof / dependency |
| --- | --- |
| ProtectedSpineOpeningCodeProof | Unreferenced import; its opened-body calculation uses actual bound substitution and literal port code, not strict marking. |
| ProtectedSpineCompletenessAbsProof | Uses only the pointwise definitional `lambdaWeak` identity from the old namespace. |
| ProtectedSpineCompletenessBasicProof | Uses the original strict-mark proposition instantiated on actual empty assignments. |
| ProtectedSpineFAbsParameterProof, ProtectedSpineCompletenessFAbsProof, ProtectedSpineCompletenessPortProof, ProtectedSpineCompletenessChecks | Transitive dependency only; preserve the same FAbs parameter, derivation induction, actual observations and both completeness conclusions. |
| ProtectedSpineAdequacyChecks, ProtectedSpineDecisionProof | Transitive dependency only; preserve the same frozen public targets, exact iff proof assembly and literal decision code. |

The narrow append-only route would clone only these nine affected files into
new parallel proof modules/namespaces, changing import/reference names but
not statements, constructions, proof premises or exact semantics. In the
OpeningCode analogue remove the unused strict import; in Abs use the same
definitional lambda identity under the new thin namespace; in Basic use the
public exact copy of the unchanged `MarkingFields` proposition. Proof details
of the unaffected soundness, lattice, premises, normalization, and all
semantic definitions can still be imported unchanged. Audit the closure to
confirm no accidental import of the old stopped supplier. The new native
audits would have new proof aliases but the existing frozen target
propositions. Do not reuse owner-host object evidence for the new closure.

Alternatively a narrowly scoped compatibility shim could use the new
supplier under the old module/export names, but that changes an owner-side
proof file. Such a change is not assumed authorized. Neither route has been
applied; both require a separately approved source-preserving review, and
each complete downstream endpoint still needs its own passing cloud native
closure. SoundRelation, SoundStage, and the accepted application gap have
no dependency on the stopped strict-mark module.
