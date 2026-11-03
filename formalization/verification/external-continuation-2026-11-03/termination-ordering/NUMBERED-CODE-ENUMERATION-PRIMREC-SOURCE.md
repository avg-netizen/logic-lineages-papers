# Primitive recursion of the original auxiliary Code enumeration

Paper06 lines551–556 requires computable finite primary classes before arithmetic coding and least-code representatives. The existing `NumberedAuxiliaryEnumeration.enumerate` is the actual finite raw-code generator used by `classCodes`, which is then decoded by `classCandidates`. This target fixes the original function jointly in every data parameter:

```lean
∀ n : Nat,
  Primrec₂ (fun
    (data : List Ty × List (HeadCode (Fin n)) × Nat × Nat)
    (bounds : Nat × Nat) =>
    enumerate data.1 data.2.1 data.2.2.1 data.2.2.2 bounds.1 bounds.2)
```

The four entries of `data` are the supplied type list, supplied head-code list, maximum label, and extra-tuple length bound. The two entries of `bounds` are the variable-index bound and recursion fuel. The head list is arbitrary input data, not silently restricted to a precomputed head window. No closure, typing, coverage, or primitive-recursion premise is added.

The exact enumeration is empty at zero fuel. A successor computes the prior list at the same variable bound and the opened list at the incremented variable bound. It then concatenates, in its original order, variable codes, lambdas, applications, bottoms, ordinary heads, numbered heads, argument nil, and argument cons. The variable range remains strictly below the variable bound; the label range remains `List.range (labels + 1)`; extra type lists come from the original `typeLists S tupleBound`. Every constructor field, ordered recursive child, repeated occurrence, and duplicate generated from the supplied lists is retained.

The intended primitive-recursion proof may use Mathlib's established finite-dependency recursion theorem `Primrec.nat_omega_rec`, with the actual fuel as decreasing measure and successor dependencies `(variableBound, fuel)` and `(variableBound + 1, fuel)`. Its combining operation must reconstruct the original ordered constructor layer from these two exact recursive results. Primitive recursion of the dependency map, combining operation, type-list enumeration, and constructor assembly must be proved; none is assumed in the target.

This establishes the genuine raw-code enumeration required by the existing `classCodes` algorithm. The separate packed-size and maximum-label bounds, original structural packed decoding, typed candidate list, exchange/saturation computation, representative-code computation, arithmetic relation, and complete source result retain their own proof obligations. No depth-effectivity or unrelated target is introduced.

## Accepted verification

The fixed statement gate and the sixteen-target focused aggregate passed
with actual transitive axiom audits. Frozen semantics and comparison hashes
are unchanged. See [the prospective freeze](CLASS-CANDIDATES-FREEZE.json) and
[the acceptance record](CLASS-CANDIDATES-ACCEPTED.json) for exact source hashes,
compiler evidence, permitted axioms and verification scope.
