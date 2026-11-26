# Local Fable-pair continuation, round 2 — 22 November 2026 (evening) — handoff

Release and parties: [RELEASE.md](RELEASE.md). Root ledger with every receipt: [root/LEDGER.md](root/LEDGER.md).
Lane ledgers: [fable2/](fable2/LEDGER.md), [opusA/](opusA/LEDGER.md), [opusB/](opusB/LEDGER.md). Evidence per
record: [evidence/](evidence/). Rules as in `../local-fable-pair-2026-11-22/BRIEF.md`.

Baseline: `a14a93677` on `formalization/github-measured-install-2026-11-22` (the external agent's commit on
top of the first round). Every result below is one bounded native gate through `scripts/check.py` with
named-axiom output (`propext`, `Classical.choice`, `Quot.sound` only); Lean is the validity check.

**Follow-up review:** the published round at `1cd1734fe` has now received an independent
statement/source assessment. See [the review and corrections](../github-round2-review-2026-11-22/REVIEW.md).
The strengthened Paper 17 main comparator and Paper 16 iteration statement have no material source
mismatch under the existing semantic interfaces. The broader realization lambda sentence remains
unresolved. The review also clarifies the application hypotheses and restores historical document
snapshots named by the evidence. No Lean source or numbered status changed in that review.

## Register

**159 checked / 8 pending / 167.** The owner promoted Paper 17 `thm:arithmetic` (#1435) and `thm:ground`
(#1436) after the external source check `../github-continuation-2026-11-22/p17/CORRESPONDENCE-REVIEW.md`
found no material mismatch, and Paper 16 `lem:structural-interpretation` (#1449) after applying the
manuscript correction (below). Pending: Paper 17 `thm:main`; Paper 16
`lem:arithmetic-accessibility`, `thm:upper`, `lem:realization`, `thm:iteration`, `lem:tower-cofinality`,
`thm:height`, `thm:main`.

## Paper 17 `thm:main` — repaired comparator proved and source scope reviewed

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

**Not promoted.** `UniformMainComparison` is a root-written comparator. The independent follow-up
[source review](../github-round2-review-2026-11-22/P17-UNIFORMITY-REVIEW.md) checks the five points
against `paper.tex` l.83–100 and finds no material mismatch under the existing semantic interfaces.
The comparator is ready for a numbered promotion decision.

## Paper 16

Gap map written before the structural promotion: [opusB/P16-GAP-MAP.md](opusB/P16-GAP-MAP.md). Its main findings:
the long internal-ID₁ line (`lem:arithmetic-accessibility`) unlocks no other statement by itself — its
only consumer is the bound in `thm:upper`, which also needs Pohlers's norm theorem, not formalized
anywhere here; `lem:tower-cofinality`, `thm:height` and `thm:main` likewise need unformalized results
of Simmons and Pohlers.

- **`lem:structural-interpretation`** — the earlier unqualified wording was false (accepted #396 is a counterexample); with the
  fixed-point qualification of `paper16/recovery-nov19/MANUSCRIPT-CORRECTION-HANDOFF.md` it is the
  conjunction now gated as #1443 ([source map](root/P16-STRUCTURAL-INTERPRETATION-SOURCE-MAP.md)).
  The owner applied that correction and promoted the statement as #1449. The independent review
  confirms the comparator against the corrected finite typed setting, including substitution.
- **`thm:iteration`, `lem:realization`** — the native statements had never compiled: as legacy roots
  they exceed the gate's memory cap by import footprint alone (root measured 1,573,864 kB against
  1,572,864 kB). Opus B made 653 module-system copies of the legacy native closure under
  `LogicLineages/NativeModule/` (645 bodies byte-identical, eight files with nine `private` modifiers removed; manifest
  `opusB/twin/TWIN-MANIFEST.json`) and both drafted proofs compiled unchanged on them: #1446 (iteration),
  #1447 (realization), peak 929,556 kB ([source map](root/P16-NATIVE-TWINS-SOURCE-MAP.md)).
  The owner chose to retain the copies, preserving the tracked legacy files. The independent review
  agrees with Opus A's iteration table and the three realization closure clauses. The remaining
  realization question is whether to prove the broader typed-lambda fundamental lemma or explicitly
  state the checked abstraction rule; its numbered status remains pending.
- **Internal application on the installed carrier** (Fable-2, three fresh sessions): for `tv := TV`,
  two accepted operand addresses with matching reports at one context and the two original type guards
  yield an accepted output address (#1438), acceptance by the installed application program (#1440),
  and output uniqueness (#1442). The general arbitrary-`tv` versions additionally require acceptance
  of the codomain by `tv`. The standalone held-least functionality theorem needs no type guards;
  the continuation results retain the original guards for application formation and least existence.

## State on disk

The round is published in commit `1cd1734feb2b64c5a9936b2b5e8649f9b2f3889c` on
`formalization/github-measured-install-2026-11-22`. It adds 700 Lean modules and the round's evidence;
the four pre-existing files changed are the Paper 16 decision source and its checksum manifest,
`CURRENT-COMPARISON-TARGETS.json` (three promotions), and `STATUS.md`. The independent review and its
documentation/provenance corrections are recorded separately under
`../github-round2-review-2026-11-22/`.

## End of round

- **Owner answers (22 November):** (1) "apply" — the fixed-point correction is applied to
  `16-persistent-marking-termination-ordering/sections/decision.tex` at both recorded sites (lemma
  statement; adequacy proof's stage induction), the paper directory's `SHA256SUMS` line is updated, and
  `lem:structural-interpretation` is promoted with #1443's comparator (numbered record #1449). The PDF
  was not rebuilt, and the two corrected passages are root's wording for the owner to edit. (2) "whichever
  you recommend" — the module-system copies stay as copies; no tracked legacy file is migrated. (3) the
  lambda clause of `lem:realization` — owner undecided; left pending.
- Also gated on the copies (Opus B): the native rank statements and the rank comparison wrapper (#1448).
  The final tree has 671 generated copies and one new assembly module: 661 identical bodies, eight
  files with nine visibility-modifier removals, and two recorded proof-term repairs.
  `thm:upper` still needs the rank = norm step (drafted, never compiled), the internal ID₁ proof and
  Pohlers's norm theorem.
- Consolidated gate over all 700 new modules of this round: exit 0, receipt
  `1795400038619106271-3265668` ([log](logs/final-consolidated-gate.txt)).
- Second Fable instance this round: three fresh sessions, $10.90 (G01 $3.19, G02 $2.73, G03 $4.98), API
  credits, no subscription fallback; $58.20 over both rounds.
- Run policy re-paused at round completion; the round was subsequently committed and published as
  `1cd1734fe`.

## Ready for the owner

1. `thm:main` (Paper 17): comparator #1445 is proved and the independent source read found no material
   mismatch under the existing semantic interfaces. It is ready for a promotion decision.
2. `thm:iteration` (Paper 16): #1446 matches the printed theorem in both the original table and the
   independent review. Promotion remains the owner's call; evidence uses the retained copies.
3. `lem:realization` (Paper 16): #1447; exact on its three closure clauses; the last sentence needs
   either the abstraction-rule reading accepted or the sentence reworded.
