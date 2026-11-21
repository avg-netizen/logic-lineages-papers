# Reachable raw scratch shape and own-run lift: source map

Local Claude root continuation, 20 November 2026. Base `26f297e41`. Supporting work for Paper 16 only;
**no numbered statement is promoted** (register stays 150 checked / 17 pending).

All statements are object derivations in the retained ID1 calculus (`Derivation body [] …`) about the
unchanged programs of `NumberedWindowInternalSparseRawTickDefinitions` and `…RawRunDefinitions`.
Callback programs `p other : Program 3`, the object body, and every term are arbitrary unless stated.

| # | Frozen target (file `NumberedWindowInternalSparseRaw…Targets.lean`) | Statement | Plan item it answers |
|---|---|---|---|
| 1 | `TickShape`: `goodState` | `∃ f F. out = stateTerm f F ∧ (f = 0 ∨ F = 0)`, both quantifiers object-level | `Good(out)` of the next-target review, same form |
| 2 | `TickShape`: `ExactOpenLiveTickShape` | `liveTick p other` on ANY ternary tape: every output has the shape | the three outer emitters; stated for an arbitrary tape, which the review needed only after row decoding |
| 3 | `TickShape`: `ExactOpenTickShape` | `chosenTick` at `![stateTerm flag frame]`, arbitrary `flag frame`, no prior shape premise | "Narrow first target" |
| 4 | `RunShape`: `ExactOpenRawLoopShape` | `goodState start → iterateState out ![fuel,start] → goodState out` | "Then lift through the actual loop"; output universally bound inside the fuel-induction motive |
| 5 | `RunShape`: `ExactOpenInitialState` | actual `initialState` graph at `stateTerm 0 (frameValueTerm q w r)` on `![q,w,r]` | the "separate open seed, not paid by #695" |
| 6 | `RunShape`: `ExactOpenOwnStateShape` | every output of `ownState` on any open tape has the shape | combination of 4 and 5 |
| 7 | `RunSuccess`: `ExactOpenOwnRunSuccessTerminal` | `ownRun = S k` on a tape ⟺ `ownState = stateTerm (S k) 0` on that tape | "separate own-run success bridge"; stated for any successor flag, which includes the numeral one |
| 8 | `RunLift`: `ExactOpenRawFirstTickShift` | given the tick graph `chosenTick next ![start]`: `iterateState out ![S fuel,start] ⟺ iterateState out ![fuel,next]` | "Exact proposed first-tick graph contract", both directions, same output term |
| 9 | `RunLift`: `ExactOpenRawTerminalExtraFuel` | `fuel < more → iterateState T ![fuel,start] → iterateState T ![more,start]` for `T = stateTerm flag 0` | extra-fuel transport; `start` and the reached `T` are distinct terms |
| 10 | `RunLift`: `ExactOpenRawRunLift` | tick `next` from `start`, `fuel < more`, terminal run from `next` on `fuel` ⟹ terminal run from `start` on `more` | 8 and 9 combined |
| 11 | `RunLift`: `ExactOpenFunctionWitnessStrict` | `child < functionWitnessTerm child` in the original object order | "strict raw child < original wrapped certificate" |
| 12 | `RunLift`: `ExactOpenLiftedOwnRun` | `ownRun = S k` on `![source,child,dest]` ⟹ `ownRun = S k` on the tag5-wrapped tape `![aux dom cod source arg, functionWitnessTerm child, aux dom cod dest arg]` | item 2 of "Remaining source obligations" for the tag5 frame |
| 13 | `RunRoot`: `ExactOpenRootTick` | at the literal root witness `rootWitnessTerm payload = rawCons 0 (rawCons payload 0)`: `rootCall p = c` on the tape ⟹ `chosenTick` returns `stateTerm c 0`, for an arbitrary supplied `c` | root branch of the tick (the review listed only its emitter shape) |
| 14 | `RunRoot`: `ExactOpenRootOwnRun` | `p = 1` at `![q,payload,r]` ⟺ `ownRun = 1` on `![q, rootWitnessTerm payload, r]` | base case that rows 7–12 lift; not in the recorded plan |

## Deviations from the recorded plan (all deliberate)

- The gap is not an explicit term `wrapped = S(child + gap)`. The premise is the original object order
  `ltF fuel more`, whose own elimination rule yields `fuel + S w = more`; the tag5 instance is then
  discharged outright by row 11, so row 12 has no order premise at all.
- The success bridge uses an arbitrary successor flag `S k`. Nothing proves that the flag is the numeral one.
- Row 4 carries `goodState start` as one uniform premise. The successor step's derivation uses only the
  induction hypothesis, but the premise is not redundant at positive fuel: a malformed start whose frame
  read is zero is returned unchanged at every fuel.

## Proof routes (suppliers are all pre-existing and unchanged)

- Emitter inversion (the "fresh gap"): `programCases` on the unknown component, forward graph rebuilt from
  `consGraph` / `compositionValue` / `constantZeroValue`, then `valueUnique` on the same emitter and tape.
  `consOfGraph` and `emitGraph` are re-established at arbitrary arity because the #689 helpers are private.
- Live dispatcher: `optionGraphCases` on `tagFiveTest` and `rootTest`, then `zeroBranchElim` /
  `successorBranchElim`. No control or callback value is interpreted.
- Tick: `frameRead`, `zeroSuccessorCases`, `zeroBranchElim` + `projectionValue` + `valueUnique` (terminal),
  `successorBranchElim` + `programCompositionCases` (live).
- Loop shape and first-tick shift: `natInduction` with an `allOne`-bound output,
  `actualOriginalRecursionSuccessorElimination` + `successorCases`, `compositionRecover` to peel projection 1,
  `recursionSuccessorIntroduction` to rebuild.
- Extra fuel: `natInduction` on the gap with the original `addZero` / `addSucc` axioms.
- Order: `rightWeakAdd`, `leftWeakAdd`, `squareSelfWeak`, `weakTrans`, `actualOriginalOrderTransitivity`.
- Root tape: `packedNode` + `literalGraph 0` (root test accepts, field zero is the payload); the tag5 test is
  rejected through `rejectForwardOrder 0 5` and the conjunction's own branches; `normalizeAccept` /
  `normalizeRecover` for the actual normalizer; the own state is one root tick followed by the #697 terminal
  loop on the witness's predecessor (the witness code is literally a successor).

## Not established

Typed raw acceptance at either tape, successful least representatives, the least-class/congruence bridge,
arbitrary-open `RawMatching`, the mixed fixed-window integration, internal ID1 membership, the
Bachmann–Howard bound and cofinality. Row 12 is machine acceptance of the scratch loop only: it says nothing
about what the accepted tapes mean. Rows 12 and 14 cover the tag5 frame and the root branch; the contextual
fallback branch (tags 1–4 and rejected tag5 frames, callback `other`) is not treated. Row 14 is about an
arbitrary `Program 3` in the root slot: it does not say that any program is the original root relation.
The numeric calibrations #690 and #695 are not used and not extended.
