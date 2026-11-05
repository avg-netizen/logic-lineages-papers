# Actual level-three seeded source systems

Baseline: `5c98e63793b3fc821965def2292e909d4436f049`.
Status: all seven exact semantic aliases passed fresh native compilation and
standard-axiom audits. Parent adoption remains pending. See SEMANTIC-ACCEPTANCE.json.

## Exact source obligation

Paper09 `hardness.tex`, `thm:functional-hardness`, distinguishes a finite-query
level-two reduction from the level-three single-query construction. Its latter
argument fixes a positive ordinal Omega whose finite-exponent projection is
zero and substitutes `x_i - Omega` for every original unknown. Original zero
polynomial unknowns are then represented by the positive value Omega.

The frozen SeededCompiler and SeededSystem targets cover the mathematical
single-query construction, using the already accepted literal closed Omega
source. They do not contain an undecidability premise or supply a numeric-code
computability theorem. The seven checked aliases remain supporting results, not the entire numbered
theorem.

## Kept semantics and quantifiers

- `SignedPair.Expression n` is the original finite signed linear Z[omega]
  grammar: unit, shared variable, addition, negation and multiplication by omega.
  It has no multiplication of unknowns. All finite original system equations
  use the same `Fin n` variable space.
- `SeededCompiler.subtractSeed` replaces every occurrence of an original
  variable with that variable minus the SAME final seed index. The actual
  compiler interprets that index by the literal CLOSED `OmegaSeed.pair`.
  No new free seed, arbitrary ordinal-valued primitive or valuation premise is
  introduced. The original free context remains `SignedPair.Context n`.
- The family lift realizes every nonnegative polynomial, INCLUDING zero,
  simultaneously as a genuine admissible source vector with signed first-field
  coefficients `embeddedCoefficients p + signedCNF Omega`. The accepted actual
  norm-padding supplier establishes admissibility; it is not assumed.
- Reverse projection uses the actual finite-exponent map. Zero projected
  polynomials are permitted and no nonzero assumption is recovered spuriously.
- Every system equation shares one original valuation. The actual source
  system builder adds exactly fresh ground alignment witnesses for its equation
  pair and preserves every original closed vector at every component. Detector
  aggregation requires simultaneous equality, not unrelated per-equation
  valuations.
- `ExactSingleQuerySemantics` proves both strict and weak query complements
  against original polynomial-system solvability, including empty systems and
  zero variables. `ExactLevelThreeBounds` retains ground output, free-variable
  levels at most one and internal levels at most three.

## Frozen comparator provenance

The recovered `SeededCompilerDefinitions.lean` and `SeededCompilerTargets.lean`
match `R007-FROZEN-TARGETS.json` exactly. The recovered `SeededSystemDefinitions`
and `SeededSystemTargets` match `R008-FROZEN-TARGETS.json` exactly. `RECOVERY.json`
records all four comparisons and all eleven recovered source hashes.

The root-adopted OmegaSeed gate is preserved byte-for-byte. Its acceptance is
`verification/local-resume-2026-11-04-six-lanes/sol5-functional/ROOT-R004-OMEGA-ADOPTION.json`.
The public archive preserved candidate sources but did not accept them; recovery
and historical partial compiler success do not replace fresh exact verification.

## Distinct remaining obligations

- Formal numeric-code computability of both actual single-query maps.
- Numerical finite-query source reduction and full coded H10-to-linear adapter.
- Genuine MRDP/H10/Narendran undecidability supplier.
- The whole `thm:functional-hardness` endpoint and whole-source promotion.

This work has no dependency on Snyatkov/BASE elimination, paper06's source
relation repair, or the separate obstructed II5 research development. It makes
no claim toward any of those obligations and edits no manuscript or old target.
