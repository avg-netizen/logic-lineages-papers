# Original sparse positive fold: sufficient-fuel terminal shape

Scope: source-first two exact supporting contracts, both object-language
derivations. No Lean evaluation or all-numeral substitution is used as
an object inference rule. Raw/least callback correctness, arbitrary-open
matching, full arithmetic accessibility and other numbered claims stay
unpaid.

| Source | Retained definition and literal obligation |
|---|---|
| `ordinals.tex:65–76,104–139` | Actual finite raw-path evidence and original positive quotient path; reduction accessibility does not follow from parser terminality. This bridge concerns the witness syntax used by the existing numerical realization, not a new reduction relation. |
| `NumberedWindowFieldAlgorithm.unpack` and actual polynomial `fieldCons` | Nil is raw zero. A nonzero raw input may be malformed, or have an actual head/tail. The proof uses all three cases of the genuine `SparseFieldInductionAtCode`, not a valid-list-only induction. |
| `NumberedWindowInternalSparsePositiveFold.lean:16–45` | The original step and recurrence; `sufficientAt` keeps the actual loopGraph, exact context/type, encoded current and original raw input. Original numerical scratch uses a private cons; the endpoint `existsOne (scratchGraph out 0 current)` is the same actual returned output and requires no positive current. |
| `...SparsePositiveFold.lean:47–51` | `OpenChosenFuelTerminal` instantiates genuine terminality at fuel equal to that same unchanged raw certificate; original arithmetic gives cert < S(cert), not an extra caller premise. |

The actual ordering formula is `InternalOriginalOrderSyntaxProof.ltF`,
the retained embedded `OrdinaryArithmetic.lessFormula`. The bound is
literally cert < successor(fuel), the source raw-code bound, not length
or certified valid-code membership. `uniformAt` is an actual `allBlock`
over [fuel, encoded current, output] with context and type remaining
fixed free terms. For induction, place the arbitrary raw code at the
new distinguished `Fin 1` coordinate and relabel only the fixed free
terms. An IH on a raw tail therefore applies to genuinely advanced
current, predecessor fuel, and the same output.

Proof route to be authored only after target preflight:

- Nil: choose the genuine `scratchGraph state 0 current` via the old
  cons program's totality. Actual nil loop at arbitrary fuel (#646)
  and actual `iterateState` functionality transport this true shape
  to the already supplied output, then introduce the object existential.
- Malformed: malformed includes genuine nonzero; `cert < S(fuel)`
  forces positive fuel independently in the actual zero/successor split.
  Choose true earlier scratch and new dead scratch (0,0); use the actual
  malformed original step (#638), actual head-first shift (#651) and
  genuine nil loop at predecessor fuel (#646). The same real output
  is terminal, not an arbitrary witness replacing the known result.
- Cons: original pair and cons order give actual raw tail < cert (#616),
  also forcing nonzero cert/fuel. After fuel=S(pred), internal strict/weak
  transitivity yields tail<S(pred). Choose the actual selected advance
  result using the unchanged program's graph totality (possibly zero),
  and actual cons scratch values. The real update step (#638) and
  actual head-first equivalence (#651) shift to tail at pred. Apply the
  original generalized IH to the same output and the advanced current.

The exact output/acceptance contracts of the finish wrapper are a
separate scope; this proof does not infer raw/least semantic
correctness or the ordered path-composition/matching theorem.
