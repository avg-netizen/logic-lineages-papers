# Next raw reachable-state target: source-only review

Reviewed 20 November 2026 after supporting 698. **Unproved plan, not a new
Lean theorem, gate, acceptance record, or numbered promotion.** No callback
semantics, typed raw relation, or least-class compatibility is inferred.

## Narrow first target

For the same physical `chosenTick p other`, define an object formula

`Good(out) := ∃ flag frame, out = stateTerm flag frame ∧ (flag = 0 ∨ frame = 0)`.

The proposed genuine object implication is

`programGraph (chosenTick p other) out [stateTerm f F] → Good(out)`.

The input must be pack-shaped; f and F may be arbitrary open terms, and
there is no prior Good premise. Keep the body fixed and use actual object
quantifiers/equalities, not a predicate on external natural evaluations.
Do not generalize to arbitrary malformed scratch bytes: the terminal
branch preserves its entire input, not a newly validated encoding.

Source reason: `RawTickOpenScratchProof.frameRead` exposes the actual F
at every `stateTerm f F`, not only the more special `liveRead` triple.
At F=0 the real terminal branch returns that same scratch. Every live
branch in `RawTickDefinitions.liveTick` has one of these outer emitters:
`emitState 0 chosenFrame`, `emitState 0 other`, or
`emitState (rootCall p) 0`. Their unknown component may be any value;
no interpretation or typed validity of that component is needed for this
outer shape invariant. In particular this does not establish that an
arbitrary fallback result is a valid typed frame.

## Exact existing suppliers and the fresh gap

- `InternalControlGraphSupportProof.zeroSuccessorCases` is the retained
  object zero/successor split. With `frameRead` and `outputTransport`, it
  supplies the real zero or successor control graph for `chosenTick`.
- `InternalAcceptanceBranchProof.zeroBranchElim` and
  `successorBranchElim` select the actual branch. The terminal case uses
  `projectionValue` and `valueUnique` on the SAME program/input to recover
  the original scratch. This is not uniqueness at different addresses.
- `InternalAcceptanceSupportProof.programCompositionCases` eliminates
  `performLive` and exposes its real row-coordinate eigenvariables. The
  live shape proof can apply to an arbitrary resulting three-slot tape;
  no decoded-frame or lexical meaning is required here.
- `NumberedWindowInternalFreshProbeProof.optionGraphCases` is already a
  generic selector over any Program arity. Its source uses actual
  `programCases`, `zeroSuccessorCases`, output transport, and relabeling.
  It can split the two nested live controls before branch elimination.
- A general object emitter-shape supplier is still fresh work. The
  `scratchState` helper in `RawTickOpenLiveProof` is PRIVATE and proves
  forward construction, not inversion. A small route is to re-establish
  its actual `consGraph` construction, use `programCases` only for the
  unknown emitter component, and compare the resulting known state
  with the supplied output using `valueUnique` on the same `emitState`
  and same tape. For the zero component use `constantZeroValue` directly.
  Alternatively, genuine composition inversion exposes both nested
  cons outputs. Neither route may substitute numeric `emitValue` for an
  object derivation.

## Then lift through the actual loop

A useful loop motive quantifies the output **inside the object formula**:
`∀ out, G(iterateState, out, [fuel, originalStart]) → Good(out)`.
Fix the original start as an unchanged parameter. The source initial
state has flag zero, so its base invariant is available, but its actual
initialState graph still needs a genuine emitter construction; supporting
695 supplied only its numerical calibration.

`actualOriginalRecursionSuccessorElimination` and `successorStepCases`
expose the exact predecessor result and the original step graph. The
induction hypothesis must be usable at that predecessor-result
**eigenvariable**, not only at a fixed output term. Peel the literal
step projection 1 using `compositionRecover` and apply the proposed
one-tick supplier after transporting the predecessor's actual state
representation. Supporting 697 proves only identity when the original
input is already terminal. It is not this invariant and must not be
reused with the original start silently identified with a reached output.

A later, separate own-run success bridge can combine this invariant with
the actual final `cellHead` graph at output one. The canonical state-head
graph and same-input functionality identify its flag with one; the
invariant then forces frame zero. This is an unproved route to the actual
terminal scratch `stateTerm 1 0`, not a result of numerical equality.
First-tick shifting, terminal extra-fuel continuation from a distinct
original start, and the polynomial parent/child own-fuel gap still need
actual graph proofs. The exact next first-tick contract and those parameter
distinctions are also recorded in the raw-machine lane handoff.

Even after these machine suppliers, original syntax/window admission,
selected raw and least object meaning, the oriented argument/least-class
bridge, RawMatching, internal I/C and the ID1/BH endpoints remain separate.

## Exact limitation on the older fiber-lift template

A separate read of `InternalOriginalObjectFiberCertifiedLiftDefinitions`
and `...Targets` confirms that `LiftAtAnyBody` ALREADY quantifies an
arbitrary body and ambient hypotheses. Merely choosing the new body does
not discharge its other parameters or premises. Its exact antecedent
uses the older Selection's `src K Gamma p`, `comp K Gamma p`, and
`lift K Gamma p`, and additionally requires

`argumentFiber Gamma a = graph1 InternalUnpair.left (numeral (Encodable.encode Gamma)) a`.

The new guarded report in 698 supplies the actual new address/fiber
report and actual endpoint scalar graphs. It is not this old left-graph
premise, nor an identification of the two selected program packages.
The older theorem remains a source construction template, not a direct
import-level replacement for the new raw/least matching obligation.
This is a scope distinction, not a new counterexample or impossibility
claim, and does not rule out a future explicitly proved bridge.
