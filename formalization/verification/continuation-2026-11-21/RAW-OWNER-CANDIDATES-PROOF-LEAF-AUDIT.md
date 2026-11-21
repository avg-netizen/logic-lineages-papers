# Independent proof-leaf audit of the five Paper 16 raw-machine candidates

Read-only review of the 25 owner Lean modules at `762b1c912`: all
`NumberedWindowInternalSparseRaw{TickShape,RunShape,RunSuccess,RunShift,RunLift,RunRoot}*`
candidate sources, including five target and five exact-check modules. The
[static reconciliation](RAW-OWNER-CANDIDATES-INDEPENDENT-REVIEW.md) remains
separate. This review follows the actual proof terms and critical inherited
suppliers; it is not a native check, an object-cache audit, or acceptance.

In the references below, `Raw...` is a filename suffix under
`LogicLineages/PersistentMarking/NumberedWindowInternalSparse`. The callback
programs remain arbitrary throughout. Uses of totality, functionality and
induction below are object-language derivations, not metatheoretic evaluation
of closed numerals reflected back into the object calculus.

## Tick shape (two exact aliases)

- `RawTickShapeTargets.lean:23–47` binds actual object flag and frame
  witnesses and asserts the literal scratch equality and
  `flag = 0 ∨ frame = 0`. It does not require the flag to be Boolean or
  the frame to decode or be typed. `RawTickShapeSyntaxProof.lean:31–106`
  verifies term/formula substitutions and renamings and introduces the two
  quantifiers at the intended slots.
- `RawTickShapeEmitterProof.lean:35–84` reconstructs the nested sparse cons
  graph for the actual emitter. The unspecified component is supplied by
  object program totality, and functionality of the same emitter on the
  same tape identifies the supplied output; the fixed component really is
  zero. No guessed decoding, inverse pairing premise or callback contract.
- `RawTickShapeLiveProof.lean:30–63` eliminates the literal tag-five and
  root branch graphs. Fallback and selected-frame emitters have zero flag;
  the root emitter has zero frame. This observes fallback *shape*, not the
  meaning of any contextual fallback result.
- `RawTickShapeTickProof.lean:37–68` reads the actual second cell
  (`RawTickOpenScratchProof.lean`, `frameRead`), splits it inside arithmetic
  into zero or successor, eliminates the literal projection in the former,
  and peels the actual live composition at arbitrary row-selector
  eigenvariables in the latter. The input is explicitly a two-field state;
  this does not generalize to malformed raw scratch bytes.

## Run shape and run success (three plus one exact aliases)

- `RawRunShapeLogicProof.lean:22–86` proves substitution and equality
  elimination for the shape formula and eliminates its two existentials
  into fresh object variables with the actual matrix and weakened context.
- `RawRunShapeMotiveProof.lean:36–108` binds the arbitrary output *inside*
  the object induction motive. `RawRunShapeInductionProof.lean:44–137`
  uses `goodState start` in the fuel-zero projection case. For a successor,
  `actualOriginalRecursionSuccessorElimination` exposes the actual prior
  output and step; the induction hypothesis is applied at that output.
  Recovering projection 1 gives the actual tick, and shape elimination
  permits transport to a literal two-field input for that tick. The
  original start remains an unchanged parameter throughout.
- `RawRunShapeOwnProof.lean:37–85` proves the forward graph of initial
  state by the three ordered projections, nested cons, successor and
  zero flag. Own-state composition uses functionality to identify the
  initial component and proves shape at the actual loop fuel. The
  underlying `RawRunDefinitions.lean:15–35` uses the same witness in the
  original tape and as fuel via projection 1; it does not consume or replace
  the witness on initialization.
- `RawRunSuccessProof.lean:37–108` constructs the actual `cellHead`
  read from canonical sparse cons. On a supplied successor read,
  functionality identifies the internal flag with that exact successor;
  successor-not-zero eliminates the zero-flag disjunct. Frame-zero and
  flag congruence give the stated terminal scratch. The reverse direction
  builds the actual own-run composition with the literal head graph.
  This is an arbitrary-successor equivalence, not an assertion of a
  particular accepted raw semantics, or that all such flags equal one.

## First tick, terminal extra fuel, and literal tag-five lift (five exact aliases)

- `RawRunShiftMotiveProof.lean:26–100` quantifies the common output at
  fixed start/next inputs; `RawRunShiftProof.lean:41–149` proves
  early-to-late shift by internal induction. In the zero case the supplied
  first tick follows the actual initial projection. The successor case
  eliminates the earlier recursor step, recovers the tick on its actual
  previous scratch from projection 1, and replays that tick after shifting
  the predecessor graph. Neither callback's behavior is hypothesized.
- `RawRunShiftProof.lean:152–169` proves late-to-early by internally
  obtaining an early output using `programCases`, shifting it forward,
  and comparing it by `valueUnique` against the supplied output of the
  *same* later recursor at the *same* inputs. The equality is transported
  into the earlier graph. This is not inverse fuel monotonicity or
  inversion of the tick on arbitrary scratch.
- `RawRunLiftProof.lean:39–134` constructs the literal zero-frame terminal
  tick, then places the **reached terminal scratch** in the previous-result
  and output positions while keeping the **original start** in the
  recursor's original-input position. Gap induction uses original
  addition equalities and keeps that same start throughout.
  `orderCases` supplies the actual positive additive gap;
  `runLift` first extends the next-scratch run by its predecessor and
  spends the remaining one unit on first-tick shift. No substitution of
  the reached terminal for the original start. The frozen `RawRunLiftTargets`
  prose says “own fuel”; the theorem correctly quantifies arbitrary fuel,
  while the final own-run lift uses actual witness fuel.
- `RawRunLiftOwnProof.lean:41–58` uses the literal successor-of-pair code
  and the inherited object inequalities `rightWeakAdd`, `weakTrans`,
  `squareSelfWeak`, and `leftWeakAdd` to place the child strictly below
  its nested wrapper. `InternalUnpairReverseBoundsArithmeticProof.lean`
  proves the square bound, including zero, internally. This is not a
  numeric sample or an external code-size premise.
- `RawRunLiftOwnProof.lean:66–108` peels/rebuilds own-state via
  `ownLoop`/`loopOwn`; the wrapper witness occupies both the witness
  slot and fuel argument. `ownRunLift`'s real tick and strict-growth
  premises are discharged in `liftedOwnRun`, using
  `RawTickOpenChecks.exact_OpenLiftedTick` with the actual wrapped tape.
  The dependency runs through `RawTickOpenLiveProof.literalLive` and
  `RawFunctionFrameOpenChecks.exact_OpenLiteralFunctionFrame`.
  `RawFunctionFrameTargets.lean:33–40` has literal tag-six endpoint
  wrappers with both shared annotations and the same raw argument,
  and literal tag-five with exactly one child witness. `RawFunctionFrameOpenGuardProof.lean:44–65`
  derives the physical guard from three shape reports and exact matching
  equality tests on slots 0, 1 and 3; the source/target child fields are
  selected from slot 2 and the witness child from slot 0. Thus neither
  guard truth nor corresponding outputs are supplied as external facts.
  The conclusion is one forward literal machine lift preserving the
  successor result; it is not general semantic interpretation of raw tag
  five or a converse for arbitrary parent runs.

## Literal tag-zero root (two exact aliases)

- `RawRunRootTargets.lean:18–42` has a literal tag-zero witness with
  exactly one payload. `RawRunRootTapeProof.lean:77–139` proves actual
  tag-five rejection by the physical head and original equality-test
  separation of zero and five, then tag-zero recognition and payload
  extraction by the exact one-field node. Its root-input graph passes
  unchanged endpoints and the unwrapped payload. `rootCallAccept` and
  `rootCallRecover` use the actual normalizer at unit.
- `RawRunRootProof.lean:67–113` composes the genuine row-selector graphs,
  selects the root branch, and emits `stateTerm c 0` for the supplied
  root-call graph. The literal witness is a successor of a specific
  pair term. One root tick and the inherited
  `RawRunTerminalChecks.exact_OpenRawTerminalLoop` therefore construct
  the whole own state. The earlier terminal supplier's fixed-tick
  premise is itself discharged by `RawTickOpenChecks.exact_OpenTerminalTick`;
  its proof is genuine recursor induction
  (`RawRunTerminal{Components,Induction}Proof.lean`).
- `RawRunRootProof.lean:115–145` builds root own-run at unit in the
  forward direction. The converse obtains the root call's actual output
  internally, constructs the own-run graph, identifies that output with
  unit by functionhood of the same own-run at the same tape, and inverts
  normalization at unit. It does not prove that a particular supplied
  program is the original root relation, nor a root-acceptance equivalence
  at arbitrary successor flags.

## Trusted boundary and disposition

Under `LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/`,
`InternalAcceptanceSupportProof.lean:14–22` derives `programCases` from
the original program-totality theorem `actualOriginalPrograms`;
`InternalControlGraphSupportProof.lean:109–117` derives `valueUnique`
from its functionality component. `InternalTagArithmeticSupportProof.lean:137–143`
builds `natInduction` using the existing object arithmetic induction rule.
The proof-leaf audit found no extra hidden hypothesis or semantic reflection
in the 13 exact aliases. The five exact-check wrappers discharge the
stated premises using the above suppliers, not new implicit semantic
contracts.

These are five supporting packets only. They do not interpret contextual
fallback tags 1–4, establish general raw tag-five semantics, discharge
the original raw syntax and packed-window guards, calibrate a chosen root
to `NumberedWindowConcreteCheckers.root`, establish least representatives
or least congruence, or give free-term `RawMatching`, source integration,
ID1 membership or an ordinal bound. No numbered promotion follows.
No native compiler was run for this audit. Historical receipts and fresh
serialized native/current-artifact and standard-axiom verification are
separate evidence. Source review alone is not grounds for adoption.
