# Paper 16 native iteration: numbered-promotion review

Continuation date: 2026-11-22 (America/Chicago).
Reviewed checkpoint: `9a8fd8f8ffd9c1ab27b91096dc1e52aa196bb413`.
Root reserves numbered record #1478; adoption and register changes are root-owned.

## Verdict

The current `NativeIteratorRealizesFullPrefix` is the printed
`16-persistent-marking-termination-ordering:thm:iteration`, with no extra
theorem premises. No mathematical or source-correspondence blocker remains.
The earlier independent review is complete, and a later actual native compile
has checked the unchanged endpoint with standard-only axioms. Numbered
promotion is justified without another compiler replay.

## Exact declarations and pins

Native source module paths:

- `LogicLineages.NativeModule.PersistentMarking.NativeOrdinalIterationTargets`.
- `LogicLineages.NativeModule.PersistentMarking.NativeOrdinalIterationProof`.

The declarations retain their original namespaces:

- Target:
  `LogicLineages.PersistentMarking.NativeOrdinalIterationTargets.NativeIteratorRealizesFullPrefix`.
- Exact alias:
  `LogicLineages.PersistentMarking.NativeOrdinalIterationProof.exact_NativeIteratorRealizesFullPrefix`.

| Source | SHA-256 |
|---|---|
| `NativeOrdinalIterationTargets.lean` | `d0ff2e54d373fa038151f7a0a44f7675bd46162b194a67b31de7ccd9f02fbd57` |
| `NativeOrdinalIterationProof.lean` | `b9387f9c5c6bbd6c9074567e868c9c4535e141545c9f89196c0e9f9381f00cf6` |
| Paper 16 `sections/ordinals.tex` | `526aa249902b4e4bf00f45bee770bdcdc9f9b39c2dc341778834600b7f8bf1b5` |

The Lean hashes match supporting record #1446. Full hashes for the previous
reviews, accepted record, and current named axiom log are retained in
`ITERATION-PROMOTION-CHECK.json` beside this review.

## Statement correspondence

The manuscript's semantic setting is countable ordinals at base type and all
set functions at arrow types (`ordinals.tex:390-391,423-432`). The convention
at lines 458-464 takes the full earlier prefix at each nonzero limit. The
theorem at lines 467-469 asserts realization by the displayed native iterator,
including nonmonotone semantic functions.

The current target at `NativeOrdinalIterationTargets.lean:24-28` has the exact
scope:

```text
∀ signature S, ∃ native well-foundedness wf,
  ∀ finite semantic type A, ∃ iterate,
    (∀ f x, full-prefix OrbitEquations for iterate) ∧
    Realizes the literal typed iterator iterate.
```

The semantic `iterate` is constrained by the zero, successor, and entire-prefix
limit equations, which uniquely determine the orbit. No monotonicity premise
is added. Its ordinal input is countable because that is the stated semantic
base, not because the theorem has been weakened. The native carrier and rank
are those of the actual closed-native confined relation. Well-foundedness is
supplied in the conclusion, not assumed from the caller.

The term is the literal three-binder iterator displayed at
`ordinals.tex:452-456`, with its original recursor, discarder, eraser, and bound
indices. Realization quantifies over closed realizers of each semantic input,
as does the paper's definition; it does not assert that all set functions have
closed realizers.

The detailed original correspondence table is
`verification/local-fable-pair-2026-11-22-round2/opusA/P16-THM-ITERATION-CORRESPONDENCE.md:21-76`.
The completed independent check is
`verification/github-round2-review-2026-11-22/P16-SOURCE-REVIEW.md:106-148`.
Their positive verdicts remain applicable to the unchanged source.

## Existing exact native evidence

An actual fresh compilation of the endpoint occurred in
`build-reports/1795406363595178414-12.json`. Its module entry reports:

- Module `LogicLineages.NativeModule.PersistentMarking.NativeOrdinalIterationProof`.
- Return code 0 and the exact proof-source hash above.
- Peak process-tree RSS 959,696 KiB within the fixed native profile.
- Named output in
  `build-reports/1795406363595178414-12-LogicLineages-NativeModule-PersistentMarking-NativeOrdinalIterationProof.log`
  gives exactly `propext`, `Classical.choice`, and `Quot.sound` for
  `exact_NativeIteratorRealizesFullPrefix` and the indexed-carrier endpoint.

Receipt `build-reports/1795407211156632997-11.json` subsequently records the
same module as a verified cache hit, using that actual compilation and matching
source hash. The original supporting receipt is
`1795399156663919873-3256109`, retained by #1446. These receipts and named
outputs already provide the required gate; this review runs no compiler.

## Dependency and claim boundaries

The unresolved final sentence of `lem:realization` does not block iteration.
The iterator uses the checked strict-backward and countable-supremum closure
clauses and transports realization through the actual three strict beta edges.
It does not invoke a general structural typed-lambda fundamental lemma.

Evidence must cite the `NativeModule` source paths. The copies retain original
declaration namespaces, so importing both legacy and native copies into one
root is not supported. Their transformation provenance was independently
reconciled before this review; no migration of frozen legacy files is needed.

Promotion of this theorem proves neither Simmons calibration nor any intended
collapse/BH supplier. Those remain separate inputs of the conditional height
and main theorems. No existing source, frozen record, or register entry was
edited by this review.
