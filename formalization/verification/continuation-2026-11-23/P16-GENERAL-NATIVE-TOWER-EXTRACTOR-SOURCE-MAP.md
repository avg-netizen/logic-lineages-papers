# Paper 16: literal original extractor at every finite level

The printed (B_l) source expression is in `ordinals.tex:532–551).
The construction uses the previously gated actual ladder (A_0=ι),
(A_{l+1}=A_l→A_l) and the original `actualType` with base native type
`indexType` (`o→o`). The literal original `NativeIteratorTargets.applied`
uses the original native `iterator` at precisely (A_l); its closedness
is the already checked `NativeIteratorChecks.exact_ClosedNativeIterator`,
instantiated at that actual type. No new erasure hypothesis is used.

| Original construct | Literal generated operation |
|---|---|
| α | nearest original bound variable at index 0 and type `indexType` |
| h_j (1 ≤ j ≤ l) | original bound variable at index j and type (A_j) |
| h | original bound variable at index l+1 and type (A_{l+1}) |
| Initial iteration state | h_l if l is positive; real closed Z when l=0 |
| Remaining application suffix | (h_{l-1},…,h_1,Z) through left-associated original `NativeReduction.app` |
| Fix wrapper | literal original `ordinalFix` applied to the abstraction over α |
| Remaining binders | (λ h,h_l,…,h_1) in the actual outermost-to-innermost order |

The binder slice lemma proves the original index shifts as each binder is
discharged, including a genuinely empty original context at the end.
The lowering proof follows strictly descending types and verifies the
literal terminal Z from the checked basis, not an arbitrary low-value
term. `extractorClosed` proves original contextual typing, original
signature validity, ordinary syntax, absence of free names and native
syntax for every (S,l). The exact aggregate includes literal equality
of the first two codes with independently checked #1463 (B₀,B₁).

No ordinal iteration correctness, helpfulness, collapse calibration,
native tower witness ranks or cofinality are claimed. This packet gives
the actual closed native *syntax* needed to remove the supplied-prefix
premise of the checked printed-(D) term assembler in a later separate
join. Native gate `LogicLineages.PersistentMarking.NativeTowerExtractorGeneralProof`;
four named axiom reports, no ordinal/Mathlib import.
