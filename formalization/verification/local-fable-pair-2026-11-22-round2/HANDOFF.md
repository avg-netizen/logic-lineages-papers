# Local Fable-pair continuation, round 2 — 22 November 2026 (evening) — handoff

Release and parties: [RELEASE.md](RELEASE.md). Root ledger with every receipt: [root/LEDGER.md](root/LEDGER.md).
Lane ledgers: [fable2/](fable2/LEDGER.md), [opusA/](opusA/LEDGER.md), [opusB/](opusB/LEDGER.md). Evidence per
record: [evidence/](evidence/). Rules as in `../local-fable-pair-2026-11-22/BRIEF.md`.

Baseline: `a14a93677` on `formalization/github-measured-install-2026-11-22` (the external agent's commit on
top of the first round). Every result below is one bounded native gate through `scripts/check.py` with
named-axiom output (`propext`, `Classical.choice`, `Quot.sound` only); Lean is the validity check.

## Register

**159 checked / 8 pending / 167.** The owner promoted Paper 17 `thm:arithmetic` (#1435) and `thm:ground`
(#1436) after the external source check `../github-continuation-2026-11-22/p17/CORRESPONDENCE-REVIEW.md`
found no material mismatch, and Paper 16 `lem:structural-interpretation` (#1449) after applying the
manuscript correction (below). Pending: Paper 17 `thm:main`; Paper 16
`lem:arithmetic-accessibility`, `thm:upper`, `lem:realization`, `thm:iteration`, `lem:tower-cofinality`,
`thm:height`, `thm:main`.

## Paper 17 `thm:main` — repaired comparator proved, awaiting a read against the paper

The external check found #1429's comparator too weak: a decider per effective policy and per near-control
parameter, where the paper says "uniformly in a supplied computable policy" and "for every supplied b".
That was a mismatch of statements, not a defect in a proof, and it is the kind of thing compilation
cannot detect.

Repair, all gated:
- [root/UNIFORM-MAIN-SOURCE-MAP.md](root/UNIFORM-MAIN-SOURCE-MAP.md): frozen `UniformMainComparison`
  (`LogicLineages/PermittedControl/UniformGroundComparisonTargets.lean`) — one partial recursive procedure
  per relation whose runtime inputs include the policy program and, at the near controls, b; halting on
  every raw input for programs realizing a policy; plus the control laws, the hardness statements and the
  literal policy-independent reduction programs.
- #1433, #1434 (external agent): supplied-code macro evaluator; effectivity ⇔ a realizing program.
- #1444 (Opus A): the source compiler with the policy program as input, calibrated to the existing one.
- #1441 (Opus B): a closed-block decider computable jointly in b.
- #1437, #1439 (root): the uniform statement implies #1428; the assembly from the two pieces.
- **#1445 (root): `uniformMainComparison : UniformMainComparison`, no hypothesis.**

**Not promoted.** `UniformMainComparison` is again a root-written comparator. The source map ends with
the five points a reader should check against `paper.tex` l.83–100. Owner decision after that read.

## Paper 16

Gap map for all eight pending statements: [opusB/P16-GAP-MAP.md](opusB/P16-GAP-MAP.md). Its main findings:
the long internal-ID₁ line (`lem:arithmetic-accessibility`) unlocks no other statement by itself — its
only consumer is the bound in `thm:upper`, which also needs Pohlers's norm theorem, not formalized
anywhere here; `lem:tower-cofinality`, `thm:height` and `thm:main` likewise need unformalized results
of Simmons and Pohlers.

- **`lem:structural-interpretation`** — false as printed (accepted #396 is a counterexample); with the
  fixed-point qualification of `paper16/recovery-nov19/MANUSCRIPT-CORRECTION-HANDOFF.md` it is the
  conjunction now gated as #1443 ([source map](root/P16-STRUCTURAL-INTERPRETATION-SOURCE-MAP.md)).
  **Owner decision: correct the manuscript**; then #1443 is the comparator.
- **`thm:iteration`, `lem:realization`** — the native statements had never compiled: as legacy roots
  they exceed the gate's memory cap by import footprint alone (root measured 1,573,864 kB against
  1,572,864 kB). Opus B made 653 module-system copies of the legacy native closure under
  `LogicLineages/NativeModule/` (645 bodies byte-identical, 8 with one `private` removed; manifest
  `opusB/twin/TWIN-MANIFEST.json`) and both drafted proofs compiled unchanged on them: #1446 (iteration),
  #1447 (realization), peak 929,556 kB ([source map](root/P16-NATIVE-TWINS-SOURCE-MAP.md)).
  **Owner decisions:** whether the copies may stand as cited sources or the tracked files should be
  migrated in place (changes hashes pinned by hundreds of records); whether these statements are the
  printed theorems — Opus A's tables `opusA/P16-THM-ITERATION-CORRESPONDENCE.md` and
  `opusA/P16-LEM-REALIZATION-CORRESPONDENCE.md` — including whether the abstraction rule is what
  `lem:realization` means by "the typed lambda fundamental lemma".
- **Internal application on the installed carrier** (Fable-2, three fresh sessions): from two accepted
  operand addresses, the application has an accepted output address (#1438), is accepted by the installed
  application program (#1440), and that output is unique (#1442). The two type guards are still held.

## State on disk

All new modules are untracked files; the only tracked files changed are `CURRENT-COMPARISON-TARGETS.json`
(the two promotions) and `STATUS.md`. Nothing is committed or pushed in this round.

## End of round

- **Owner answers (22 November):** (1) "apply" — the fixed-point correction is applied to
  `16-persistent-marking-termination-ordering/sections/decision.tex` at both recorded sites (lemma
  statement; adequacy proof's stage induction), the paper directory's `SHA256SUMS` line is updated, and
  `lem:structural-interpretation` is promoted with #1443's comparator (numbered record #1449). The PDF
  was not rebuilt, and the two corrected passages are root's wording for the owner to edit. (2) "whichever
  you recommend" — the module-system copies stay as copies; no tracked legacy file is migrated. (3) the
  lambda clause of `lem:realization` — owner undecided; left pending.
- Also gated on the copies (Opus B): the native rank statements and the rank comparison wrapper (#1448).
  `thm:upper` still needs the rank = norm step (drafted, never compiled), the internal ID₁ proof and
  Pohlers's norm theorem.
- Consolidated gate over all 700 new modules of this round: exit 0, receipt
  `1795400038619106271-3265668` ([log](logs/final-consolidated-gate.txt)).
- Second Fable instance this round: three fresh sessions, $10.90 (G01 $3.19, G02 $2.73, G03 $4.98), API
  credits, no subscription fallback; $58.20 over both rounds.
- Run policy re-paused; nothing is committed or pushed in this round.

## Ready for the owner

1. `thm:main` (Paper 17): comparator #1445 proved; needs a read against the paper
   (`root/UNIFORM-MAIN-SOURCE-MAP.md`, last section), then promotion → Paper 17 complete.
2. `thm:iteration` (Paper 16): #1446; Opus A's table says it is the printed theorem; promotion is the
   owner's call (evidence exists only on the copies).
3. `lem:realization` (Paper 16): #1447; exact on its three closure clauses; the last sentence needs
   either the abstraction-rule reading accepted or the sentence reworded.
