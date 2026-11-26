# Current17 `lem:inner-termination`: source map of the frozen target

Target: `LogicLineages.PermittedControl.InnerTerminationTargets.FullInnerTermination`
(`InnerTerminationTargets.lean`). Frozen before proof in `INNER-TERMINATION-FREEZE.json`. Written by the
local Claude root on 21 November 2026. **No independent pre-scope review was run**; this map is the
author's own correspondence argument.

## Printed statement

`arithmetic.tex` 164–195. A strict order of the r distinct raw coordinates gives ranks 0,…,r−1. For one
row, 𝓜 is the sum of 3^rank(x) over the active count occurrences and 𝓥 is the number of ordinary nonlinear
value occurrences; identical syntactic fields are combined and zero coefficients removed. The lemma: every
exact zero-class replacement strictly decreases 𝓜+𝓥, and neither summand increases.

## Formal objects

| Paper | Target module |
|---|---|
| Row with combined fields and no zero coefficients | `Row O ι r`: finitely supported integer coefficients on ordinary fields `O` and on count fields `ι × Fin r`, plus a constant |
| Count occurrence τ_P(x) | a pair (interval label, input); the input is its rank in `Fin r` |
| 𝓜 | `countCharge`: Σ over the support of the count coefficients of 3^rank |
| 𝓥 | `valueCount`: size of the support of the ordinary coefficients |
| Class sharing the full value C, zero combined leading coefficient | subsets `T` (ordinary) and `S` (counts) of the supports, not both empty, with `2·Σ_T b + Σ_S a = 0` (the paper's integer test 2b+Σaᵢ=0) |
| Equation (zero-replacement): ordinary occurrences disappear, each τ_{Pᵢ}(xᵢ) becomes aᵢ·τ_{Pᵢ'}(xᵢ) + aᵢκᵢ | `R'.value` is `R.value` with `T` removed; `R'.count` is `R.count` with `S` removed plus the replacement terms; `R'.const` adds the shifts |
| Identity and short prefixes become constants | `Disposition.ended` |
| Equal-input prefixes merge; the smallest surviving input is kept | `Disposition.survives`, admissible only at the surviving input `x0`; all survivors give the one field `(q, x0)` |
| Transfer (rank-transfer): τ_{P'}(y) = τ_{Q'}(x) − τ_H(x) for x<y | `Disposition.transferred (some h)`, admissible only strictly above `x0`: the field `(q, x0)` minus `(h, x0)`; `transferred none` is the case where τ_H is a constant |

## What is and is not modelled

- Interval labels and ordinary fields are abstract types. The lemma is about the charge, which depends
  only on ranks and on which fields occur; the target therefore holds for every label set, in particular
  for the paper's finitely many interval, certificate, peeling and transfer labels.
- The relation `ZeroClassReplacement` is deliberately at least as wide as the paper's operation: the class
  may be any subsets with the zero test, a transfer need not have a survivor, and new fields may coincide
  with fields outside the class (they are then combined, and removed if they cancel).
- The target does **not** say that the replacement is exact for the actual entry norms and interval counts,
  that cores coincide, or that the collision table forces the transfer. Those are `lem:count-transfer`,
  which stays pending. Nothing here evaluates a field.
- Pattern guards, linear raw coordinates and annotations carry no charge in the paper and are not
  represented.

## Proof route (for orientation only)

Ordinary side: 𝓥' + |T| = 𝓥. Count side: the new support lies in (old support ∖ S) ∪ the fields of the
replacement terms. An ended member contributes nothing, a survivor at most its own weight, a transferred
member of rank j at most 2·3^(j−1) < 3^j. If T is empty then Σ_S a = 0 with all aᵢ ≠ 0, so |S| ≥ 2; either
some member is ended or transferred (strict), or all survive and at least two equal-rank occurrences
become one field (strict).
