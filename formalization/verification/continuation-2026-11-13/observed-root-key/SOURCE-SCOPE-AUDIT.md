# ObservedRootKey source-scope audit

Status: independent read-only audit found no scope mismatch. Final native exact gate passed per coordinator receipt `1794568925851946848-12`. This audit was refreshed against the repaired accepted InitialProof; evidence status remains coordinator-owned. No compiler or proof-source edits performed.

## Same tuple and exact conclusion

`ActualRootKeyPreservation` uses precisely `ObservedPut.finalInputs`, `ObservedPut.finalData`, and `ObservedPut.key`, with their original window, source-premises and fold-graph antecedent. Its conclusion is the root structural-key graph iff at the SAME mark and runtime parameter. There is no Accepted, key equality, child preservation, canonical-output or fixedness premise.

`ObservedRootKeyProof` instantiates the new traversal theorem at `ObservedPut.prepared p H G W`. This matches the definition of ObservedPut.refined: `OriginalAllPositionStructuralTraversalDefinitions.refined` on that prepared tuple. WorkingDefinitions, LeafProof and TraversalProof open the all-position namespace; ClosureProof and ActivationProof explicitly name that same refined tuple. No new wrapper calls the older `OriginalStructuralTraversalKeyDefinitions.refined` or its minimum inputs. Imports of old structural-key modules provide generic field identities, constructor congruence and wrapper reasoning, not replacement of the observed tuple.

## Actual minimum and component recovery

The working minimum is `OriginalClassContextAllPositionSelection.inputs (OriginalStructuralClassKeyDefinitions.inputs p H G W) H G W P`. InitialProof obtains its actual domain from the all-position condition. Crucially, the final accepted version does NOT identify rawData.oldRepresentative directly with the observed minimum: it derives minimum preservation, uses `OriginalAllPositionGuardedIndexedProof.initialRepresentative` to expose the additional rank/activation guard, and lifts preservation through that wrapper using `OriginalStructuralKeyWrapperProof.observedPreservation`. The earlier candidate lacked this substantive guard step; the initial static audit did not detect that elaboration gap, so its earlier wording about a projection identity is superseded here. MinimumProof calls `OriginalAllPositionMinimumSupportProof.minimumHit` on the actual all-position representative graph, not the old active-kernel minimum theorem.

`acceptedRecover` yields `Old Accepted AND all-position Tests`. Taking its left component is correct. `matrixFromRelation` then yields `candidate Domain AND (keyGraph AND observerGraph)`. Consequently `andLeft (andRight hm)` is exactly the old representative's keyGraph, not the observer/rank component. At the structural-input instantiation this old representative is the intended pre-minimum structural key. `keyTransfer` and `indicatorIff` derive the same-mark iff from an internally queried value, with no supplied value-equality premise.

## Closure and final fold

The selected OTHER leaf's old-preservation supplier is proved by InitialProof, not assumed by the endpoint. Application/lambda closures recover input/output activity and literal constructor fields at the new refined tuple and use existing generic structural-key congruence. Payload induction consumes these proved closures. Final traversal conversion uses the generic final-canonical equivalence, window identity and selected source-premise identities at that SAME refined tuple.

This establishes only root-key preservation. It is not equality of folded endpoint syntax, equality of arbitrary observers, hereditary evaluator equivalence, Object fixedness/cancellation, or full internal I/C/accessibility. It does not identify ObservedPut.finalData with the older PutIntegration tuple.

## Reviewed source fingerprints

- `ObservedRootActivationProof.lean`: `f6bf072711d14a924f8a1196659a70506044906d4e3034c0d8b7611d0b3e9386`
- `ObservedRootClosureProof.lean`: `16edbf5bea2af770fcf0edc1e4e6defe9f5080757ff67e59bbf9344b37c6e2e2`
- `ObservedRootInitialProof.lean`: `4f98d0236df30ab1bac7b6253cb56e1b579dae726ca758980a94f60258ab70f3`
- `ObservedRootKeyPreflight.lean`: `86cac4cd09280df700f95ce36d20c78070bd561e0132a4a673c0ca8acfb5f38b`
- `ObservedRootKeyProof.lean`: `ca12f153688e03beded3279ee0dbb9c7e533d7add7c2d26cef04c8f227892394`
- `ObservedRootKeyStatementChecks.lean`: `488c82fa8c0c33e43ae351777a09a05e71fc79cfa4739e30e56770a74732a185`
- `ObservedRootKeyTargets.lean`: `9843b635a9abe2476d610869b25d91fc95e9377dd523e575697918440e4c6206`
- `ObservedRootLeafProof.lean`: `00aca1a918328f573a8d20b24505962e123c8a0d24d3c377793fa483132b7536`
- `ObservedRootMinimumProof.lean`: `67d5fe54d0ce9b825e85d108542c9afe2ef2d1ebc7b2398d705f8053e50bd473`
- `ObservedRootTraversalProof.lean`: `b1db39964b5ada579e2bb8d8d394fa452b5f8d9116ccae4233163a8b91cbe711`
- `ObservedRootWorkingDefinitions.lean`: `efd2517d8e940c829f3be5a5ca4a2538ba66cc66c808f45527e6a9d3c835e398`
- `Erasure/ObservedPutTargets.lean`: `901cc8378b78da68ffa4e042acff255b6cde457862f0913f1b4acb5d79f706cc`
