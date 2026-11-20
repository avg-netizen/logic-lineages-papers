# Original sparse positive fold: genuine chosen-code cons recurrence

Scope: two exact supporting arbitrary-open formulas on the unchanged
selected programs. Neither raw nor least callback correctness, original
address-wrapper equivalence, arbitrary matching, or internal accessibility
follows from this result.

- `ordinals.tex:70–76,115–127` uses actual positive finite certificate
  paths. The recurrence here pays the original numerical helper for
  an actual raw ordered field list, not a new definition of the
  source relation.
- `NumberedWindowFieldAlgorithm` and `...InternalSparsePair.fieldCons`:
  actual supplied raw cell `consGraph cert head tail`, with the same
  unmodified head and tail and original polynomial code. The successor
  is exactly `S((head+tail)^2+head)`; no use of dense scratch pairs
  in the raw-code bound.
- `...InternalSparsePositiveFold.lean:30–51` and actual
  `...SparsePathAdvanceTargets.selectedGraph`: the same context,
  type and encoded current feed the actual selected advance on the
  head. Its true result may be zero, as may cert's tail. The exact
  same `raw`/`least` programs feed both sides. No positive
  source path for the tail is required.
- `...SparsePositiveFold.lean:47–57`: `OpenChosenStateCons`
  compares the actual arity-four `chosenState` graphs at original
  (ctx,type,current,cert) and (ctx,type,next,tail). Each uses that
  call's literal raw code as fuel. `OpenFinishCons` compares the
  corresponding actual `finish` graphs, with no prescribed output
  code or added terminal premise.

Planned exact derivation after target preflight:

1. The retained original sparse cons equation (#616) gives
   `cert=S(pred)` at the actual polynomial predecessor, and its
   original tail bound gives `tail<cert`. Ordinary `weakOrderCases`
   gives an actual arithmetic additional fuel witness
   `tail+extra=pred`, not an external choice of numerals.
2. Given true tail chosen-state output, #657 ensures it has a
   genuine scratch pair with cursor zero. At the same actual loop
   result, #646 adds arbitrary extra fuel to tail. The actual
   step-update (#638) and head shift (#651) relate the predecessor
   loop to the original raw certificate at successor fuel. The
   outputs agree by original graph functionality. Compare both
   actual graphs, using graph totality to supply the comparison
   input in each direction. #654 ties the exact chosenState AST
   to those same loop calls.
3. The actual same returned state and true terminal scratch
   give the actual finish value on both sides (#655). Transport
   that value to the original supplied output by actual
   functionality. No positive/nonnil-tail conclusion is claimed.
