# Paper 17: raw rendering of the canonical linear exit

Key: `STAGE-CALLBACK-RENDER-LINEAR`. Targets module
`LogicLineages.PermittedControl.StageCallbackRenderLinearTargets`.

Printed source: `17-permitted-control-canonical-comparison/sections/arithmetic.tex`,
`thm:arithmetic`: "If z has no remaining nonlinear occurrence, retain the entire row as a linear row
in z, with its correlated lower-input fields as parameters, and stop." This key is the code-level
form of that one retained row; it is the `linear` field of `StageCallbackRawLevel.Rendering` (#1398).

## What is stated

A raw program on encoded data only:

- `lowerCode top`, `slopeCode top`, `namesCode i` — the rank filter, the total weight at the greatest
  rank, and the plain-variable items of the lower slots, as folds over the raw term list;
- `rowCode`, `atomCode`, `testCode`, `polarityCode` — the row data, its nonnegativity atom, the
  order test (tag 0 equality as two inequalities, 1 nonnegativity, otherwise strict positivity) and
  the requested polarity on the radix-six formula code;
- `linearCode top s order positive` — groups the raw syntax with the accepted `groupRaw`, then the
  table bytes and the formula code.

Targets:

- `ExactLinearCode` — for every `top`, typed syntax `s`, order test and polarity,
  `linearCode top (encodeSyntax s) (orderCode test) positive
     = encodePacket (canonicalPacket top s.constant s.terms test.test positive)`.
  This is literally `Rendering.Exact.linear` for `R.linear := linearCode`.
- `LinearCodeEffectivity` — `Primrec` for each component and for `linearCode` (uncurried).

## What is assumed

Nothing. No hypothesis on syntax, ranks, activity or `f`.

## What is not claimed

- Nothing on raw input outside the encoder image, and nothing for order tags above 2 (read as strict
  positivity; `orderCode` never produces them).
- Not the guard rendering and not the congruence rendering; `Rendering.Exact` needs those as well.
- No semantic statement: that `canonicalPacket` means what it should is #1375/#1394.
