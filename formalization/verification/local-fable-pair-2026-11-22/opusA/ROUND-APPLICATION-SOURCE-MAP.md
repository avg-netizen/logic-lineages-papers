# Round application — source map (Opus A, task 3, 2026-11-22)

**Serves.** Paper 16, "all statements respect the finite equivalence quotient", function-side
closure `Q R_S Q' ⇒ Qx R_S Q'x` on classes: the application of every member of the function's
reached pool to a fixed argument has the same successful least as the application of the seed.

## (a) `…RoundApplicationTargets` — generic round induction, application motive
`appMotive N C X W s ctx ty dom cod arg μ m k := unary N μ k ⊓ leastGraph C X W s ctx ty (auxiliaryTerm dom cod k arg) m`.
The function-level edge program `E`, the measure program `N` and the application-level programs
`C X W s` are independent parameters.
- `ExactRoundApplicationLeastAt`: under the *relative* one-edge premise `ApplicationEdgeStepAt E … Γ …`
  (an accepted `E`-edge `w → k` carries the motive, asked in every renaming-extension of Γ), the seed
  motive, `roundGraph E out i vertices fctx fty seed` and `memberGraph out k` give the motive at `k`.
- `ExactRoundApplicationLeast`: the #835-style formula version under the context-free premise
  `ApplicationEdgeStep` (`SameLeastOnEdge` style).
The premise is relative because on the combined programs the step needs held facts (type guards,
argument window); a context-free premise could not use them. Inputs: premise, seed motive.

## (b) `…RoundApplicationCombinedTargets` — the actual combined programs
- `MeasurePreservingEdge E N`: the single remaining premise about an exchange.
- `ExactCombinedApplicationLeastStep`: least half of the step, from a shared measure of `w` and `k`
  (no premise).
- `ExactCombinedApplicationEdgeStepAt`, `ExactCombinedRoundApplicationLeast`: under
  `MeasurePreservingEdge (edge4 X W) (selectedMeasure P.R)` only (plus guards, argument window, seed
  measure μ, seed application least m).
- `ExactMeasuredExchangePreservesMeasure`: for the guarded paired exchange over
  `measuredExchange M D`, any C s M D W, the premise is a theorem.

## (c) `…RoundApplicationRepresentativeTargets` — the seed's own least
- `ExactLeastRepresentativeApplication` (generic): the function's packed least `x` (programs
  `Cf Xf Wf sf`, members over `edge4 Xf Wf`) satisfies the seed's application motive, under the
  relative premise for `edge4 Xf Wf`.
- `ExactCombinedLeastRepresentativeApplication`: unmeasured chosen exchange, under
  `MeasurePreservingEdge`; inputs guards, argument window, seed application least `m`, function least `x`.
  Conclusion: the application of `x` has least `m`. The seed measure is derived (totality).
- `ExactMeasuredToPlainEdge`, `ExactMeasuredCombinedApplicationEdgeStepAt`,
  `ExactMeasuredCombinedRoundApplicationLeast`, `ExactMeasuredCombinedLeastRepresentativeApplication`:
  the function-level round / least use the measured exchange `Xm`; the application least uses the
  chosen unmeasured `X`. No measure premise.

**Not claimed.** That `MeasurePreservingEdge` holds for the unmeasured exchange (it does not in
general). A single-exchange measured version (application least also over `Xm`). Existence of the
seed application's least (it is an input). Anything about different raw representatives.
