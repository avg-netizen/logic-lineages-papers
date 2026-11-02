> SUPERSEDED COVERAGE RECOMMENDATION: the kernel theorem is valid, but whole
> `lem:context` is provisional pending actual equivariance and a fresh-binder
> context bridge. See [source-scope correction](../CONTEXT-SCOPE-CORRECTION.md).
> The historical promotion recommendation below must not be used as current
> whole-source acceptance.

# Whole-source review: paper06 `lem:context`

Source: `06-godel-t-termination-ordering/paper.tex`, lines475–486.
The original statement says that replacing ordinary a by b in any ordinary
context preserves strict comparison whenever a strictly compares to b.

`LiteralContextStrictClosure` covers every constructor of the literal typed
one-hole grammar: hole, both application positions, lambda, and every ranked
argument. Holes may be open in their actual local binder context. The named
`FullNamedContextStrictClosure` retains literal lookup/shadowing and erasure,
not an alternative relation. All untouched arguments use proved ordinary
reflexivity; actual Stat and Select dependencies are discharged. Type-support
and confined-context targets are additional interfaces, not premises added
to the original strict-context theorem. No source statement is modified.

Root source review authorized this sole promotion before integration. After
independent10alias acceptance and the40alias focused aggregate pass, all
original clauses are paid. The register advances135→136checked and52→51pending;
2inherited statements are unchanged. Strong-pair/stability, substitution,
transitivity, well-foundedness and ordinal realization are not inferred.

Public validation is the adjacent source/hash/alias summary. Detailed internal
compiler artifacts are not part of this public payload. This is not a full-root
or CI pass, and does not recover unavailable historical proof bytes.
