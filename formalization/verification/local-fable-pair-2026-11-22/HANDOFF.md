# Local Fable-pair round, 22 November 2026 — handoff

Release, rules and parties: [RELEASE.md](RELEASE.md), [BRIEF.md](BRIEF.md). Root ledger with every receipt:
[root/LEDGER.md](root/LEDGER.md). Lane ledgers: [fable2/](fable2/LEDGER.md), [opusA/](opusA/LEDGER.md),
[opusB/](opusB/LEDGER.md). Evidence for every record: [evidence/](evidence/).

Baseline `1bd0f9d9a` on `formalization/new-paper-set-2026-11-18` (fetched, 628 commits ahead of the
previous local tip). Numbered register unchanged by this round: **156 checked / 11 pending / 167**.
Supporting records added: **#1386 onward** (see the table at the end). Every record is one bounded native
gate through `scripts/check.py` with named-axiom output (`propext`, `Classical.choice`, `Quot.sound` only)
plus the authoring lane's scope note. No proof-body review and no cross-model review were done; Lean is
the validity check, as the owner asked.

## Paper 17

**The comparator for `thm:arithmetic` is proved with no hypothesis**: `closedBlockDecision :
ClosedBlockDecision` (#1418, `LogicLineages/PermittedControl/StageCallbackGuardRenderCloseProof.lean`).
`ClosedBlockDecision` (`ClosedBlockDecisionTargets.lean`) says: at the factorial control and at every near
control there is a computable procedure answering the existential, negated and universal closed-block
queries of #1372 on every encoded topological circuit and plain prepared matrix.

How it was closed, in dependency order:
1. #1387 the high callback contract for any shaped, exact per-row packet supplier, given the literal
   emission equation; #1388 the legacy supplier inhabits the interface.
2. #1394/#1395 the canonical (first-occurrence) supplier is exact; #1397 its level-order variant, the one
   an executable program can emit, with its stage contract.
3. #1398 the raw per-row level program, calibrated to the level-order supplier for any exact rendering
   record; #1409, #1410, #1416 the linear-exit, congruence and comparison-guard rendering programs;
   #1404 the append/join codes.
4. #1393 the raw properness filter; #1405–#1408 predecessor guard, projection, decode, reify and the
   assembled child program.
5. #1411–#1415 the assembled raw `high`, its emission equation and computability, and the close
   conditional on the rendering record; #1396 the reduction of the comparator to a computable emitter.
6. #1389 the join regression (projection after the join keeps the shared-coordinate constraint).

**Not promoted.** `ClosedBlockDecision` is a comparator root wrote this round. Opus A compared it with
the printed theorem phrase by phrase from the definitions:
[opusA/P17-THM-ARITHMETIC-CORRESPONDENCE.md](opusA/P17-THM-ARITHMETIC-CORRESPONDENCE.md). Its verdict: it
is the printed theorem in the paper's flattened matrix language, with four named conventions (matrix
linear in circuit nodes; universal blocks range over successful runs; correctness only on admitted
encodings; sharing carried by the form of the statement) and one thing not re-checked (that
`collapseWith` is the paper's ψ_f, which rests on earlier accepted records). **Owner decision:** accept
that correspondence and promote `thm:arithmetic` (register 157/10), or ask for a review first.

**`thm:ground` and `thm:main`:** [opusA/P17-GROUND-GAP.md](opusA/P17-GROUND-GAP.md) finds `thm:ground` is
assembly of accepted pieces and `thm:main` is `thm:ground` plus accepted #339 and #010. **Both
comparators were then proved with no hypothesis**: `GroundComparison.groundComparison : GroundComparison`
(#1428) and `GroundComparisonMain.mainComparison : MainComparison` (#1429), from the ground domain
(#1424), the positive-coordinate test (#1425), the reduction (#1426), the scalar-to-circuit compiler
(#1423), the assembly (#1427) and #1418. **Not promoted** either; correspondence tables with the named
conventions: [thm:ground](opusA/P17-THM-GROUND-CORRESPONDENCE.md) (vectors of different lengths compared
with zero padding; one decider per policy, control and relation; correctness on encoded typed terms
only) and [thm:main](opusA/P17-THM-MAIN-CORRESPONDENCE.md) ("uniformly in the policy" formalised as "for
every effective policy"; "permitted" carried by the control-law clauses of #010, no formalisation of
Wilken–Weiermann §2.1). If the owner accepts all three correspondences the register becomes
159 checked / 8 pending with Paper 17 complete (33/33).

## Paper 16

The 22 November cloud handoff planned to reach equal minima through mutual inclusion of the reached
pools. That route is not needed: accepted #818 already gives equal minima for every guarded exchange.

- #1386 opposite paired parent exchange ⇒ equal successful leasts at the two applications.
- #1390 both leasts exist and are one value (existence from the thin matching window report #1338).
- #1391, #1392 the shared measure hypothesis moved from the applications to the functions.
- #1399 internal induction over actual rounds with an application motive; #1400 on the combined programs
  under one named premise (accepted edges preserve the selected measure); #1402, #1403 application
  factors through the function's least representative.
- #1401 the measured exchange satisfies that premise; #1419, #1420, #1421 the single-exchange step, the
  round and the representative statement entirely over the measured exchange, no measure premise;
  #1422 class-level congruence: functions with the same packed least have applications with the same
  packed least.

**Open design point (owner / next round).** The combined route's installed exchange is the directed
exchange, which carries no measure comparison; the measure-preservation premise is false for it in
general. Everything above is premise-free only for the measured exchange
`guardedExchange P.cover s (thinPairedExchange (measuredExchange (selectedMeasure P.R) (directedX base P.V)))`,
which is not of the `directedX` form, so records stated for `directedX` do not transfer by substitution.
Installing the measured exchange in the combined programs is the natural next step and was not done.
Still held as inputs in #1421/#1422: the two type guards, the argument window, and the existence of the
application leasts.

## State on disk

- All new `.lean` modules are untracked files under `LogicLineages/PermittedControl/` and
  `LogicLineages/PersistentMarking/`; no tracked `.lean` file was edited. Failed drafts are kept under
  [drafts/](drafts/). Nothing is committed or pushed.
- `AGENTS.md`, `README.md`, `TARGETS.json`, `CURRENT-COMPARISON-TARGETS.json`, the manuscripts, the
  toolchain and `scripts/` are untouched.
- Second Fable instance: `.claude/tools/claudep/claudep`, API-credit route throughout, no subscription
  fallback observed. One session resumed for four turns ($41.84), then fresh narrow sessions on the
  owner's request (F01 $3.30, F02 $1.98). Receipts: `fable2/*-receipt.json`.

## End of round

- Consolidated gate over all 108 new modules: exit 0, every module a verified cache hit against its
  passing receipt, receipt `1795388841702636941-3166500` ([log](logs/final-consolidated-gate.txt)).
- 44 supporting records, #1386–#1429, 119 gated theorems: [RECORDS.md](RECORDS.md). Source pins re-hashed
  at the end: no mismatch. No `sorry`, `axiom` or `native_decide` in the new sources.
- Run policy re-paused (`.local-run-policy.json`; the round's open policy is archived as
  `ROUND-LOCAL-RUN-POLICY.json`). No lane, provider process or compiler is running.
- Second Fable instance total: $47.30 on API credits (one session resumed four times $41.84, smoke test
  $0.18, fresh sessions F01 $3.30 and F02 $1.98); no subscription fallback.

## Decisions waiting for the owner

1. Promote `thm:arithmetic`, `thm:ground`, `thm:main` (Paper 17) on the three correspondence tables, or
   have the comparators reviewed first. Root left `CURRENT-COMPARISON-TARGETS.json` untouched.
2. Commit and push (nothing is committed).
3. Paper 16: install the measured exchange in the combined route (see above), then derive existence of
   the application leasts so that #1422 needs no held least call.
