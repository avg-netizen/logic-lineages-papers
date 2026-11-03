# Original09 signed polynomial pairs — fresh reconstruction

Source: `09-canonical-source-expressivity/hardness.tex`, `lem:pair-compiler`.
This work does not claim to recover any lost October31 proof bytes. It does not
include `thm:functional-hardness` or supply its undecidability prerequisite.

## Comparator domains

- `Expression n` has unit, finite-indexed variable, addition, negation and omega
  shift. Arbitrary finite integer coefficients and omega powers enter through
  the executable `fromMonomials` adapter. An atom has at most one unknown, so no
  unknown-by-unknown product is introduced.
- All `n` context entries are exactly `tau = o -> o`. Generated outputs are
  genuine existing `OriginalTerm (Context n) tau` values, not arithmetic nodes
  masquerading as sources. Renaming gives unused fresh de Bruijn binders.
- `signedCNF` maps the actual omega-CNF finite coefficients into `Int` and retains
  the actual ordinal exponents. The signed group is `Ordinal ->₀ Int`; it does
  not subtract ordinals or truncate a negative coefficient at zero.
- `omegaShift` maps exponent `e` to `e+1`, i.e. `1 ⊕ e`. No finite-exponent
  projection is performed. Quantification is over *every* original admissible
  substitution, including transfinite functional heads.
- `InternalLevelBound 2` is the existing entire-source subtype support predicate,
  including the types of the recursor, lambdas and intermediate applications.
- The coordinates are obtained from the existing total actual assignment API;
  both are separately asserted positive. Only their signed-CNF difference may
  have negative coefficients.

## Compiler correspondence

`project` is literal P, `liftOmega` is literal H using the original recursor
argument order, and `join` uses the accepted literal FunctionalDetector.combine
(S). `unitPair` is a complete balanced height-four S tree with 8 positive-12,
5 negative-19 and 3 zero leaves; `variablePair` has three factor-eight paddings
followed by S with the constant pair. `pad d` uses factors eight and sixteen
with exponents `d/3 + (2-d%3)` and `d%3`, adding exactly `d+6` to the scale.
Addition aligns at `max(k1,k2)+6` and returns exponent `max(k1,k2)+9`.
Negation swaps outputs and H increments the exponent by one.

## Intended exact acceptance gate

`SourceSignedPairStatementChecks.fixed_signed_pair_compiler` has precisely
`Targets.SignedPairCompiler`, and `fixed_monomial_adapter` has precisely
`Targets.MonomialAdapter`. The populated gate was written before any candidate
proof. Definitions/Targets must compile, receive root source review, and have
all three hashes frozen before candidate authorship. Current files are drafts
until those steps return successfully; no completion claim is made.
