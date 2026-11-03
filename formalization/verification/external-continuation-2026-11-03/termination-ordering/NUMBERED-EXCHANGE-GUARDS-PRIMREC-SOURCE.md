# Effective literal head equivalence and argument permutation

Paper06 lines551-556 requires computable primary classes before selecting
least-code representatives. The original exchange algorithm compares the
original head classes and permutes complete typed base arguments. These two
fixed targets establish primitive recursion of those exact decisions on the
accepted structural-code presentations.

Head equivalence is the original `RecursiveComparison.headEquivalent` applied
to the literal `decodeHead` of both supplied head codes. No precedence,
head-window, result-type or base-type assumption is introduced. Permutation is
the literal `List.Perm` decision on lists of `(Ty, Code)` pairs, retaining each
argument's type, structural code and multiplicity. It does not identify terms
merely by untyped syntax or support sets.

These are supporting guards. They do not replace target-head membership in
the actual `sourceHeads` list, establish whole exchange-checker correctness,
or complete primary-class, representative or arithmetic accessibility claims.

## Accepted verification

The fixed statement gate and the thirteen-target focused aggregate passed
with actual transitive axiom audits. Frozen semantics and comparison hashes
are unchanged. See [the prospective freeze](PRIMARY-CLASS-PRIMREC-FREEZE.json) and
[the acceptance record](PRIMARY-CLASS-PRIMREC-ACCEPTED.json) for exact source hashes,
compiler evidence, permitted axioms and verification scope.
