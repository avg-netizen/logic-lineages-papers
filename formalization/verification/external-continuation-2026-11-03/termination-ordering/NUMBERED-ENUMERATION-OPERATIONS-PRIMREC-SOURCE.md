# Exact type-list and source-head enumeration operations

Paper06 lines551–556 asserts that primary classes are finite and computable because only finitely many heads from the finite type window and permutations occur. The existing auxiliary code enumerator obtains its type lists and coded heads from `NumberedAuxiliaryEnumeration.typeLists` and `sourceHeads`. These targets retain those actual functions:

```lean
Primrec (fun p : List Ty × Nat => typeLists p.1 p.2)

∀ (n : Nat) (arity : Fin n → Nat),
  Primrec (fun p : List (Fin n) × List Ty => sourceHeads arity p.1 p.2)
```

`typeLists S 0` is `[[]]`; a successor stage prepends the empty list and conses every supplied type onto every list from the preceding stage. The target preserves the original order and multiplicity, including duplicates in `S`, and the original enumeration of lists of length at most the bound.

`sourceHeads arity symbols S` is exactly `(headWindow arity symbols S).map headCode`. The underlying raw list begins with zero and successor, then the case/recursor heads in the original order, the ordered application-head product, and the supplied ranked symbols. The original `HeadInWindow` predicate filters this list before coding. Its original result and base-argument signatures, actual arity table, ordering, and repetitions remain unchanged.

The target does not substitute unrestricted `HeadInWindow` truth for membership in the actual head enumeration. For arbitrary non-closed `S`, these need not agree: raw case and recursor annotations are drawn from `S`, while the guard tests their full result types. No subtype-closure assumption is added to the computation targets; the separate existing enumeration-completeness theorem retains that assumption. Both input lists vary, and every finite signature size and arity table is included.

A candidate may use primitive list recursion and list construction for `typeLists`, and exact map/filter calibration for `sourceHeads` together with the accepted head constructors and head-window decision. The accepted `HeadCode` and type presentations are used directly, without introducing a separate encoding of `Head`. These operations support the original code and typed-candidate enumeration. They do not by themselves establish primary-class reachability, least-code representatives, arithmetic edge interpretation, or the whole source theorem.

## Accepted verification

The fixed statement gate and the sixteen-target focused aggregate passed
with actual transitive axiom audits. Frozen semantics and comparison hashes
are unchanged. See [the prospective freeze](CLASS-CANDIDATES-FREEZE.json) and
[the acceptance record](CLASS-CANDIDATES-ACCEPTED.json) for exact source hashes,
compiler evidence, permitted axioms and verification scope.
