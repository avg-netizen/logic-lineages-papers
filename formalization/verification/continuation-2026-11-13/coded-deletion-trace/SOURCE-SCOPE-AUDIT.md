# Independent source-scope audit: coded deletion trace

Reviewed CodedDeletionTraceDefinitions, Targets, StateProof, StepProof, Proof, and the reused DeletionChainDefinitions. Native result reported by coordinator: exact1 PASS, receipt 1794569814177545522-6. This audit adds no compiler claim.

## Findings

- `steps` is an arbitrary object-language arithmetic term (`OTerm alpha`), not an external Nat/Fin index. `allRows` applies internal `natInduction`, then eliminates its universal at the actual term `steps`.
- `AllSteps` is one internal bounded universal formula. Its body asks for `StepAt` at each cutoff below the symbolic step count. `StepAt` is an internal existential block of 13 terms, not an external family of assumed semantic derivations.
- Each step contains literal original raw-list lookups at index and successor index; literal nested-pair projection programs recover the state and current deletion metadata. The `record : Program 7` constructor is defined, but its graph is not a premise: records are used through their actual projection graphs. The claim is about those decoded records, not construction or existence of a trace.
- The reused `Transition` contains only actual current/next parameter pairs, current context length, bounded cutoff, selected-type lookup, deletion graph, and the two actual packed-term erasure graphs. It contains no admission, evaluator equality, key equality, or intermediate-result semantic predicate.
- Only the initial state has an assumed `AdmittedPair`. Successor admission/evaluator agreement is obtained from the internal induction hypothesis and the checked one-step erasure theorem through `DeletionChainProof.step`.
- Initial and final states are actual lookup/projection predicates at indices zero and `steps`. `stateTransfer` uses lookup functionality and projection equality to identify the endpoint requested by the target with the endpoint decoded by the step, rather than assuming these are the same records.
- The target explicitly retains actual list length `suc steps`. The final proof names this premise `_length` and does not use it: the operational step/endpoint lookup assumptions already suffice for preservation. Thus the theorem is stronger than necessary concerning this geometric premise, but it does NOT establish that traces exist or derive their lengths.
- The same R,H,G,M,W are maintained, and one outer parameter c is shared by all transitions. For a zero-step trace, c and context structure need not be constrained by a transition; endpoint identity alone suffices.

## Scope verdict

The source supports genuine internal symbolic-count preservation of initial original-source admission and common evaluator output along the supplied operational coded trace. It is not merely the earlier external finite-chain schema, and no intermediate AdmittedPair or endpoint equality is smuggled into the trace definition.

It does not prove existence of traces, normalization, equality of all arbitrary family-R depths, Object/canonical fixedness, final-fold endpoint equality, I/C, or accessibility. In particular it does not overcome the separate family-zero=R caveat.
