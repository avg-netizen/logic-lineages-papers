# Internal single-slice induction — frozen targets

Date: 7 November 2026.

These target and definition bytes were frozen before proof authorship. The
correspondence is a supporting internal induction interface for paper06
`lem:id1`, preserving the original scalar and multiset accessibility operators,
the unchanged literal graph compiler, the closed context numeral, and the one
combined tagged ID1 calculus.

`ActualInternalPairedClosure` transforms two actual untagged slice-closure
derivations into the existing literal combined-body closure derivation.

`ActualInternalSliceInduction` derives membership-to-invariant at either original
tag from only the selected untagged operator's closure derivation. The other
slice is left at the current predicate and its closure is discharged internally.
Both targets admit every expanded-language first-order formula, with arbitrary
predicate polarity, free parameters, assumption context and symbolic term.

The proof suppliers are the existing original I/J fixed-point equations,
tagged-invariant selection, ordinary substitution and binder transport, and the
existing one-body leastness rule. No calibration, standard-model truth,
accessibility, second inductive definition or source-closure premise is added.
The source-specific multiset/constructor/lambda closures and all-term endpoint
remain pending; these supporting targets do not promote a numbered statement.

Compilation is pending the root coordinator's sole compiler slot. Acceptance
requires exact aliases of these target types and standard-axiom closure checks.

Before proof authorship, the Definitions namespace-opening list was corrected
to include `SourceComputabilityFormulaSupportProof`, which owns `numeral`.
The original hashes are retained in `INITIAL-FROZEN-TARGETS.sha256`; the current
freeze differs only in that namespace resolution, with unchanged definitions
and target propositions.

## Source correspondence

The source is `06-godel-t-termination-ordering/paper.tex`, lemma `lem:id1`
(the arithmetic accessibility proof). Its proof first combines the separate
unnested I and J operators with disjoint tags. It then uses I-induction for
inverse application, lambda closure and singleton multisets, and nested
J-induction for multiset union and constructor base/extra multisets. The new
rule discharges the unselected tagged branch internally while preserving the
arbitrary first-order invariant and every parameter used by those inductions.
It does not prove those remaining source-specific closure arguments.

## Compiler-only target correction

The first compiler pass accepted Definitions and found that Lean parsed the
unparenthesized `instantiate theta ...` consequent as the function `instantiate`
itself in `formula.imp instantiate`. Parentheses now delimit the intended
consequent. No binder, argument, premise, connective or mathematical claim was
changed. The preceding hashes remain in `BEFORE-PARSE-CORRECTION.sha256` and the
original frozen text is recoverable from that same recorded change. Compiler
receipt: `build-reports/1794091424726354266-2.json`.
