# Source scope audit: list sum bounds and unsorted-child targets

Source-only review. Coordinator reports ListSumBound exact2 PASS `1794575593003662334-54`; this note does not independently claim evidence/publication or acceptance of the separate UnsortedChild candidate.

The sum is the actual original numeric listRec weighted fold with identity weight, not an external decoded-list sum. ActualSumBound has only its actual sum graph premise and proves sum≤raw for every numeric code. Its proof internally strongly inducts on arbitrary raw code. Zero uses the actual nil equation. Cons queries the actual tail sum, obtains its bound from the strictly smaller actual tail IH, and uses the literal fold equation plus original pairing-sum and successor-cons bounds. Nonnegativity is arithmetic, not an assumed semantic property.

ActualEntryBound retains actual length, actual internal in-range index, actual lookup and actual sum graphs. Its independent internal strong induction excludes nil from range, identifies index0 lookup with the actual head, and at successor transports length/index/lookup to the genuine tail. Tail entry≤tailSum and tailSum≤head+tailSum yield the desired bound. No native membership, decoded list, already-bounded entry or desired conclusion is assumed; repeated entries contribute repeatedly.

The new UnsortedChild targets are correctly narrower than a generic permutation oracle: ActualSortedEntryBound assumes the SAME actual original sort output plus actual input-list lookup, and concludes that input entry≤output code. A valid intended route is identity-weight sum invariance under sort, input entry≤input sum, and output sum≤output code. No permutation or sorted membership is an extra premise.

ActualUnsortedChildDescent retains original full E envelope, positive tag4 or tag5, the SAME sorted row selected by original ordinary RR or numbered RRRL path, actual sort from the supplied unsorted row, and actual in-range lookup typed=pair(type,childE) in that INPUT row. Thus child≤typed≤sorted≤payload<recursive≤out; positivity pays strictness even though sorted-entry comparison is weak. It makes no inference that the unsorted list code itself is≤sorted code. No hidden native membership/source-rank calibration or desired strict bound appears in the target.

These suppliers do not establish source-child correspondence, a rank decoder, final rank calibration or numbered I/C. No concrete scope defect found in the accepted sum route or proposed unsorted target.

```text
c4859da7219899f867455110785669a5c90e390216e50ba243d3bda67430d847  LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/SourceComputabilityCompletion/SixSol20261113/Erasure/ListEntryBoundProof.lean
5ce34dbba92878aa5bb84aa80913fc26fe2970df2be3619d7db93597f8976054  LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/SourceComputabilityCompletion/SixSol20261113/Erasure/ListEntryCoreProof.lean
1581bf70f6b6553aa1af9bd68846b7dbfd7b3871ae7e9b4701b26e14b0e3d4f5  LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/SourceComputabilityCompletion/SixSol20261113/Erasure/ListEntryInductionBindingProof.lean
3fadbfcb49cfdcfd1acd08c55138e27e4df6f8bdf07eac782342c6551a43b0c5  LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/SourceComputabilityCompletion/SixSol20261113/Erasure/ListEntryInductionDefinitions.lean
7e5ba2912e2fad6fc376183f5dafbd824afd36dd1feb5f10c90001e21b94a327  LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/SourceComputabilityCompletion/SixSol20261113/Erasure/ListEntryInductionSyntaxProof.lean
ce44ac11c21cefb963fb518c7ec8ce0399769a966a56bad66aa29ea99b831d2f  LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/SourceComputabilityCompletion/SixSol20261113/Erasure/ListSumBoundDefinitions.lean
c7868519178cb4c689a08c4137726302042539db6b357bc7ad73b629dd87f66a  LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/SourceComputabilityCompletion/SixSol20261113/Erasure/ListSumBoundPreflight.lean
7b895e4987fe6bae308a3254e84010dcda5d81f61464f9a8ba89c51e6530f6c4  LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/SourceComputabilityCompletion/SixSol20261113/Erasure/ListSumBoundProof.lean
793e98a64f5dab96b4b07bbbb8bb78649124ef96a23d43b79b6185f2a9e585af  LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/SourceComputabilityCompletion/SixSol20261113/Erasure/ListSumBoundStatementChecks.lean
14f83c258bf0d9ebfa305d456a8e6ae527c40c596f8d6fad62e44484feaf7b0e  LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/SourceComputabilityCompletion/SixSol20261113/Erasure/ListSumBoundTargets.lean
a2bf54315756fcca57bc9fc2ecb2a58788fff292e022aab4904898e1921940f7  LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/SourceComputabilityCompletion/SixSol20261113/Erasure/ListSumCoreProof.lean
54ff3a6a9fbfc2d0541f5c73a2fc71dac61c9553881ba972d99ec3b2eb31119f  LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/SourceComputabilityCompletion/SixSol20261113/Erasure/ListSumInductionBindingProof.lean
d74adee0f9c44f5175143b4d40ccf52cbd91a22c656f13573b4396fa5da7e3ce  LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/SourceComputabilityCompletion/SixSol20261113/Erasure/ListSumInductionDefinitions.lean
d4cd928fa398b767d4777116ed90e4e7ee5d7020d1c21816be890abdd47db7cc  LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/SourceComputabilityCompletion/SixSol20261113/Erasure/ListSumInductionSyntaxProof.lean
59410c883d13ddf32aab2293e6324a257e636b8a4b16f04aa5362e37963319f3  LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/SourceComputabilityCompletion/SixSol20261113/Erasure/UnsortedChildDefinitions.lean
8ee0fec193153f08bb777849d27c5edc333e61d45794440e6aafc5b3eaa97d83  LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/SourceComputabilityCompletion/SixSol20261113/Erasure/UnsortedChildPreflight.lean
06cb513fc55e9f5e9e526545cc42598a8cbf6d53737ee1532a63769e534f2e6e  LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/SourceComputabilityCompletion/SixSol20261113/Erasure/UnsortedChildTargets.lean
```
