# Current17 `lem:field-comparison`: source map of the frozen target

Target: `LogicLineages.PermittedControl.FieldComparison.FullFieldComparison`
(`FieldComparisonTargets.lean`). Frozen before proof in `FIELD-COMPARISON-FREEZE.json`. Written by the
local Claude root on 21 November 2026. **No independent pre-scope review was run**; this map is the
author's own correspondence argument. Of the three targets written in this round this one contains the
most modelling of the author's own: the printed lemma speaks of "an effective finite Boolean form" without
fixing a syntax, and the syntax below is a choice.

## Printed statement

`arithmetic.tex` 57–93. The ordinary value fields are E_P(x), f^a(E_P(x)) and f^a(x). On each fixed order
of the raw coordinates, every comparison of ordinary value fields has an effective finite Boolean form in
which the greatest raw coordinate occurs only linearly; nonlinear parameters in that form are fields on
strictly smaller coordinates.

## Formal objects

| Paper | Target module |
|---|---|
| f^a(x), bare coordinate x | `ValueField.iterate a` (a = 0 is the coordinate) |
| E_P(x), f^a(E_P(x)) with P = (λ, μ) | `ValueField.entry a λ μ`, λ and μ normal-form notations below ε₀ |
| value of a field | `FieldValue f F u v`: iterates of f, and the norm at the genuine first entry of the actual descent from λ + (u − N(λ)) into [μ, μ+ω) |
| finite Boolean form | `ComparisonForm`: `const c` (0 less, 1 equal, 2 greater) or `linear sign H` |
| the form is linear in the greatest coordinate, with a field parameter on the smaller one | `FormHolds`: in the linear case there is the value h of the field H **at x** and the accepted table row `InverseTableRows sign y h vG vF`, whose only uses of y are y < h, y = h, h < y and the unit shifts y ≤ h, h+1 ≤ y, y ≤ h−1, h ≤ y |
| effective | `distinctForm`, `sameForm`: explicit Lean definitions on notations, accepted by the compiler as computable (not `noncomputable`): natural subtraction, notation addition, subtraction and comparison, and the accepted certificate code |
| order branch x < y | `DistinctInputForm`: F is read at the smaller coordinate, G at the greater |
| "identify equal raw coordinates" | `EqualInputForm`: both fields read at one coordinate; the form is always a fixed answer |

The other placement on the branch x < y (the first field at the greater coordinate) is the same statement
with the two fields exchanged: a row decides all three relations.

## The normalizer against the printed proof

- "Cancel common outer applications of f by injectivity": the exponent differences b − a and a − b.
- "peel one last f … Each such step decreases the remaining fixed iterate count … Only finitely many
  endpoint advances μ + ωj occur": the endpoint μ + ω·c with c the exponent difference, as the notation
  `mu + omegaMultiple c`. Proved as `entry_peel`: E_{λ,μ}(x) = f^c(E_{λ,μ+ωc}(x)) from the accepted
  cocycle and the accepted short-entry count.
- "For primitive entries at x<y, Lemma gap-input fixes the answer if the larger-input map has at least
  the larger gap": `const 0` when the comparison of the two gap notations is not `lt`.
- "Otherwise the inverse threshold table makes it a comparison of y with an entry at x, with its exact
  equality condition": `linear sign (entry 0 λ_P (μ_P' + δ_Q))` with the accepted certificate code as sign.
- "At equal inputs use the gap and equal-gap certificates": `sameForm` on two entries.
- "A field at the larger input is greater than that input and hence greater than a smaller bare
  coordinate": `const 0` for an iterate at x against an entry at y.
- "A larger bare coordinate compared with a lower-input field is already linear in the larger
  coordinate": `linear 1 H` with H the remaining iterate or entry at x.
- "Identity versus identity is raw order": `iterate` against `iterate`.

## Clauses

`ShortEntryIterate` (a short entry E_{μ+ωk,μ}(x) is f^k(x), with count k), `FieldValueUnique`,
`FormWellFormed` (every linear form has sign ≤ 2 and a proper parameter field), `DistinctInputForm`,
`EqualInputForm`. The last two hold for both selected controls, for every pair of fields whose entry
intervals are proper and not short, beyond a tail T that depends only on the two fields and the control.

## Limits of the target

- **Short intervals.** An entry field must carry a long interval. A field with a short interval equals a
  bare iterate by `ShortEntryIterate`, but deciding from (λ, μ) that an interval is short and reading off k
  is not a program here. The paper reaches the same place by peeling to the identity convention.
- **Tail.** T is asserted to exist; it is a maximum of accepted effective tails and of ordinal norms, but
  no computable tail function is stated. The paper chooses one common effective cutoff later.
- **Effectiveness.** The normalizer is an explicit computable Lean definition. There is no
  `Primrec`/`Computable` theorem for it on raw codes, which is what the accepted Paper 17 targets for
  programs state.
- **Parameter fields.** H is proper but may itself be short; it is not normalized further.
- Only comparisons of two fields; rows, counts, congruences and the order normalization loop are not here.
