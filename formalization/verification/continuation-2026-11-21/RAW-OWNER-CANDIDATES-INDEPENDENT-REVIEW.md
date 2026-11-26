# Independent Paper 16 raw-machine candidate reconciliation (2026-11-21)

Read-only source and historical evidence comparison of upstream `762b1c912` against
the prior cloud checkpoint `26f297e41` and its November 20 raw-machine lane handoff.
The 25 owner Lean files are retained unchanged. These are five **supporting
candidates**, not accepted records or numbered promotions. The following counts
are inclusive local source closures (public/meta imports included); the pin
counts are the exact per-packet source maps, not the recursive closure counts.

| Exact checks root suffix | Exact aliases and actual source boundaries | Suppliers and source-leaf pins / local closure |
|---|---|---|
| `RawTickShapeChecks` | `exact_OpenLiveTickShape`, `exact_OpenTickShape`: actual live dispatch for any ternary tape and actual tick from an explicitly two-field `stateTerm flag frame`; output has two actual object existential fields and `flag=0 ∨ frame=0`. No prior flag invariant or callback semantics; no arbitrary malformed scratch input. | Literal live/wrapped branch eliminators, `frameRead`, and same-emitter functionality after genuine nested sparse cons graph reconstruction; 6 / 1201. |
| `RawRunShapeChecks` | `exact_OpenRawLoopShape`, `exact_OpenInitialState`, `exact_OpenOwnStateShape`: actual loop with explicit `goodState start`, unchanged original starting term, arbitrary fuel/output; genuine initial graph with zero flag and successor of the ordered raw triple; every actual own-state result has the shape. | TickShape and retained arithmetic/recursor induction binding arbitrary output in its motive; actual own-state AST uses the same witness on fuel/input positions; 12 / 1207. |
| `RawRunSuccessChecks` | `exact_OpenOwnRunSuccessTerminal`: actual run output `S k` iff actual own-state output is `stateTerm (S k) z` on the identical tape. General successor, not merely numeral one. Pure scratch/flag behavior, no typed raw meaning. | RunShape, actual `cellHead` graph and functionhood; 15 / 1209. |
| `RawRunLiftChecks` | `exact_OpenRawFirstTickShift`, `exact_OpenRawTerminalExtraFuel`, `exact_OpenRawRunLift`, `exact_OpenFunctionWitnessStrict`, `exact_OpenLiftedOwnRun`: same two programs and same out in both directions at `[S fuel,start]` versus `[fuel,next]` given the actual tick; larger fuel preserves reached terminal at the same original start by actual object strict order; literal tag5 witness strictly exceeds its child and lifts genuine child own-code success, retaining actual tag6 annotations and shared raw argument. | RunShift and RunShape/Success, retained object arithmetic, original literal #689 tick and #697 terminal loop. Original start is not substituted for reached terminal. The general run-lift fuel is arbitrary despite “own fuel” in its frozen comment; the final own-run lift uses the true wrapper witness at both slots. 21 / 1273. |
| `RawRunRootChecks` | `exact_OpenRootTick`, `exact_OpenRootOwnRun`: actual tick on literal tag0 one-payload sparse witness at the supplied `rootCall` graph; own-run unit iff the supplied physical root program returns unit at unwrapped payload, with identical endpoint terms. No additional general successor-flag equivalence or source root calibration. | RootTape selector/normalization facts, RunLift shift and #697; 25 / 1280. |

Thus these owner files address the former reachable-state, genuine initial-state,
first-tick, terminal extra-fuel, and forward literal tag5 own-run steps. They add
the literal tag0 base. They do not prove a converse by downward fuel extension,
interpret contextual fallback tags 1–4, identify a particular chosen root with
`NumberedWindowConcreteCheckers.root`, or furnish the two raw syntax guards and
the two packed-window admission guards of original `windowStep`. They do not
supply successful least representatives, least congruence, free-term
`RawMatching`, fixed source integration, internal ID1 membership, or an
ordinal bound. The old handoff is historical, not a list of steps to duplicate.

## Static pin and historical native evidence

The owner records are in [local continuation](../local-claude-continuation-2026-11-20/).
Recomputed all 43 `SOURCE-PINS.json` hashes and all five packet pin maps with
zero discrepancies. The candidate's linked source-map, statement-review and
evidence digests match current bytes. All 1,284 union module source hashes
match both the historical evidence and the historical shared receipt and all
1,284 receipt return codes are zero. Every module in each local static closure
is in that evidence. All 13 new named aliases have a standard-only axiom report
(`propext`, `Classical.choice`, `Quot.sound` or a subset); the evidence JSON
also reports four reused exact aliases, not four new results. The source map’s
14 rows include `goodState`, a formula definition rather than a fourteenth alias.

Owner final receipt `1795225303715897504-2677471` requests all five full
names, records successful verified cache hits, and preserves original Mathlib
limits (2048 MiB heap, 1536 MiB RSS, free threshold 2048 MiB, 90 CPU seconds,
180 wall seconds, one thread). The owner copy, combined wrapper log and
read-only evidence audit are present in the repository. The referenced
per-module earlier native receipts, module logs and compiled object bytes have
owner-machine paths and are not supplied as a complete independently replayable
artifact bundle in this checkout. This reconciliation checks current source
hashes against evidence, not the owner's old object bytes or current input keys.

| Owner artifact | Recomputed SHA-256 |
|---|---|
| `SOURCE-PINS.json` | `14decf434f8c4747162380af862158903397333d33da2539499791ff021bb572` |
| `CANDIDATE-SUPPORTING-RECORDS.json` | `254f689e4eeac1d33dd6ca3a5869185e81f181f8ccf866d83367e58c74fb0f38` |
| `RAW-REACHABLE-SHAPE-LIFT-ROOT-EVIDENCE.json` | `074b5a5a0a2710ee92bb1ebef2615854748a42dda48880ba9208e695f01f9b76` |
| `final-gate-receipt-1795225303715897504-2677471.json` | `6d4c2b9c983ccc124dd96b336f7d9552536f1c7226bdda456a54c841a87fd1cd` |
| `logs/final-gate-2.log` | `eb8ab8e20afee863381d5638f97ee955093039c70311be2d6c1e04b210fe6b76` |
| `logs/root-verify-2.log` | `073842f7d3d0db3c322b3b5508129dd675f336e5fa886dd5ba7e69dafdba2780` |

## Still pending downstream

1. Full independent cross-model proof-leaf/object review. This document is a
   statement, named-supplier and static pin/evidence reconciliation. The owner's
   review itself explicitly declares same-family statement-only scope.
2. Fresh serialized current-cloud exact union gate at original Mathlib caps,
   full source/input-key/object/receipt/archive audit, and coordinator adoption.
   No native ran in this review. No candidate is accepted by this document.
