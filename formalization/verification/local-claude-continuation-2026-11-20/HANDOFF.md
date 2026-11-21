# Handoff — local Claude root continuation, 21 November 2026 (UTC)

State: 25 new Lean modules under `LogicLineages/PersistentMarking/` (`NumberedWindowInternalSparseRaw{TickShape,RunShape,RunSuccess,RunShift,RunLift,RunRoot}*`),
all untracked, nothing committed or pushed. Register unchanged: 150 checked / 17 pending. Fourteen frozen
statements, thirteen `exact_…` theorems, one final gate, evidence and review in this directory
(`SOURCE-MAP.md` is the index). `.local-run-policy.json` was re-paused at the end of the round; the policy used during
the round is archived beside this file.

## What the raw machine lane now has (open, retained calculus, arbitrary callbacks)

1. Every reachable scratch is the two-field pack with flag zero or frame zero (tick, loop, own state).
2. A successor own-run flag is equivalent to the terminal own state `stateTerm (S k) 0`.
3. First-tick shift both ways; extra fuel at a terminal scratch under the original object order.
4. Root branch: own run on `![q, rootWitnessTerm payload, r]` reads one iff the root program outputs one at
   `![q,payload,r]`.
5. Tag5 frame: an own-code successful child run lifts to the wrapped parent tape.

Items 1 and 2 of "Remaining source obligations" in the raw-machine lane handoff are thereby paid for the root
and tag5 branches.

## Next, in order of how much is already in place

- **Converse of the tag5 lift** (parent own-run success ⟹ child own-run success). Machine side is nearly
  there: `shiftEarly` gives the child loop at fuel `wrapper − 1`; what is missing is fuel *descent* at a
  terminal output (`iterateState T ![more,start] → iterateState T ![fuel,start]` is false in general, so the
  route is totality + the shape invariant + a minimal-fuel argument, or the original polynomial own-fuel
  bound). Not started.
- **Fallback branch** (tags 1–4, rejected tag5 frames): needs open graphs of the selected `other` callback at
  literal context nodes, as #684 did for tag5. `ExactOpenRawRunLift` already takes any supplied tick, so only
  the tick graphs and the strict witness order per tag are missing.
- **Numeric identification** `rootWitnessTerm payload ↔ packNode 0 [payload]` is by definitional reading only.
- Item 3 of the lane handoff is untouched: typed raw acceptance, both least representatives, the
  least-class/congruence bridge, `RawMatching`. Nothing here bears on it beyond supplying the machine facts
  that the singleton rule #681 consumes.

## Decisions left to the owner or coordinator

- Whether to accept the five candidate packets as supporting records (and under which numbers), and whether
  the same-family review suffices or a cross-model review is wanted first.
- Commit and push: not done here.
- `AGENTS.md` still shows the 20 November cloud release as current; this lane did not edit it.
