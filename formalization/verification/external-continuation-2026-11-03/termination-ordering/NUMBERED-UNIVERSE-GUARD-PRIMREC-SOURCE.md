# Exact local universe-guard primitive recursion

Paper06's effective fixed-type auxiliary universe is tested by the existing `NumberedNumericCarrier.universeTest` and `argumentsUniverseTest`. The independently specified `NumberedUniverseRequests.guard` isolates exactly the contribution from a request's root; the existing typed expander supplies its ordered recursive children. This comparator establishes primitive recursion of that literal guard:

```lean
∀ (n : Nat) (arity : Fin n → Nat),
  Primrec (fun p : (List (Fin n) × List Ty) × Request n =>
    NumberedUniverseRequests.guard arity p.1.1 p.1.2 p.2)
```

Both window lists and the full original request remain input data. The existing request presentation retains its context, expected type or type list, and literal raw code; no replacement encoding or new effectivity premise is introduced. All finite alphabet sizes and arity tables are included, with no subtype-closure assumption.

The frozen guard checks membership of the expected result type for every term request. Lambda requests additionally check their original domain annotation. Ordinary and numbered heads additionally use the exact original `HeadInWindow` decision on the decoded head code, preserving original head-result and base-argument types even when the numbered term has a different output type. The other term constructors contribute only the result-type membership test, and every argument request contributes `true`.

These cases apply to raw requests exactly as written. Invalid term/argument constructor combinations are not replaced by `false` inside this guard; rejection remains the existing typed expander's responsibility. The guard also retains its original treatment of contexts, numerical labels, explicit result annotations, extra-type lists, and application domain annotations. Their required checks occur in the separate typed expansion and recursive requests.

A candidate may combine primitive list membership, the independently frozen exact head-window supplier, the accepted request equivalence, and the accepted literal one-constructor `CodeView`. The comparator does not assume primitive recursion of the recursive universe test, substitute an abstract predicate for it, or claim the complete universe validation result. Exact one-layer semantic calibration and bounded worklist evaluation have separate targets.

## Accepted verification

The fixed statement gate and the sixteen-target focused aggregate passed
with actual transitive axiom audits. Frozen semantics and comparison hashes
are unchanged. See [the prospective freeze](UNIVERSE-PRIMREC-FREEZE.json) and
[the acceptance record](UNIVERSE-PRIMREC-ACCEPTED.json) for exact source hashes,
compiler evidence, permitted axioms and verification scope.
