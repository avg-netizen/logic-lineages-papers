# Exact head-window decision primitive recursion

Paper06's effective fixed-type auxiliary universe requires the actual finite head-window guard used by `NumberedNumericCarrier.universeTest`. This supplier fixes the existing predicate from `NumberedFiniteUniverseDefinitions.lean`, including its original result and base-argument types:

```lean
HeadInWindow arity symbols S f :=
  RankedCovered symbols f ∧ headResult f ∈ S ∧
    ∀ tau ∈ headArguments arity f, tau ∈ S
```

The exact comparator is uniform in both finite input lists and the accepted literal head-code presentation:

```lean
∀ (n : Nat) (arity : Fin n → Nat),
  Primrec (fun p : List (Fin n) × List Ty × HeadCode (Fin n) =>
    decide (HeadInWindow arity p.1 p.2.1 (decodeHead p.2.2)))
```

`decide` uses the original `NumberedFiniteUniverse.headInWindowDecidable` instance and the existing equality instance on `Fin n`. `decodeHead` retains all six native/ranked constructors. The target keeps both lists as input data, allows duplicates and empty lists, and includes `n = 0`. No `SubtypeClosed` premise is required to decide the predicate; that premise belongs to the separate theorem establishing completeness of the finite head enumeration.

The window retains membership of the original `headResult` and every original `headArguments` entry. In particular, case and recursor heads test their actual case/recursor result types; no additional membership test for their annotations is inserted. Application heads retain their result and ordered arrow/domain base types. Ranked heads retain symbol coverage, the ground result, and their actual finite-arity ground argument list. A numbered term's retyped output does not replace these original head-signature guards.

A candidate may compose primitive list membership and bounded universal list checks with the accepted `headResultPrimitive` and `headArgumentsPrimitive` theorems. The latter derives effectivity of every actual `Fin n → Nat` arity table from its finite domain by `Primrec.dom_finite`; no oracle or new effectivity premise is supplied. The accepted `HeadCode`, `Ty`, and list presentations remain unchanged. The target proves the head guard only; primitive recursion of the full recursive universe tests and numeric carrier operations requires separate exact suppliers and calibrations.

## Accepted verification

The fixed statement gate and the sixteen-target focused aggregate passed
with actual transitive axiom audits. Frozen semantics and comparison hashes
are unchanged. See [the prospective freeze](UNIVERSE-PRIMREC-FREEZE.json) and
[the acceptance record](UNIVERSE-PRIMREC-ACCEPTED.json) for exact source hashes,
compiler evidence, permitted axioms and verification scope.
