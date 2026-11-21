# Worklog — local Claude root, third round, 21 November 2026 (UTC)

Owner goal: complete another numbered register statement. Single lane; compiler only through
`scripts/check.py` with the unchanged Mathlib profile. Nothing committed or pushed. Owner instruction
during the round: review is not necessary as long as the Lean compiles and the targets are unchanged.

- Chose paper 17 `prop:threshold`: frozen target `FullThreshold`, full consumer drafts behind a parked
  Guard resource stop. Re-hashed the six freeze pins: all match.
- Rebuilt suppliers through `ThresholdCombinedTailProof` (`logs/warm-combined-tail.log`).
- Reproduced the Guard stop (`logs/guard-01.log`, receipt 1795230759039185265-2690829): 16 s CPU,
  807,428 kB anonymous memory. Elaboration, not import footprint.
- Rewrote `ThresholdGuardProof.lean` so `omega` only sees abstract naturals: pass (`logs/guard-02.log`).
- `ThresholdEndpointProof` passed as drafted (`logs/endpoint-01.log`).
- Full gate, first run (`logs/full-01.log`): NumericCalibration and Unequal pass; Equal fails on a
  `rw … at` whose pattern is absent from one hypothesis. Fixed with `simp only … at`.
- Second run (`logs/full-02.log`): Equal, NumericPrograms, PartialPrograms pass; Base fails on
  `Part.mem_map_iff` (explicit function argument) and one reversed equation. Fixed, same fix in Translated.
- Third run (`logs/full-03.log`): `ThresholdStatementChecks` passes, receipt 1795231090968427178-2693071,
  290 modules, standard axioms only. Recursive evidence: 0 errors (`logs/threshold-root-verify.log`).
- Record 700 written; register entry set to checked; counts 152 / 15; STATUS.md updated; policy re-paused.

Tracked files changed this round: `ThresholdGuardProof.lean`, `ThresholdEqualProof.lean`,
`ThresholdBaseProof.lean`, `ThresholdTranslatedProof.lean`, `CURRENT-COMPARISON-TARGETS.json`,
`verification/new-paper-set-2026-11-18/STATUS.md`.
New files: `accepted/700-threshold.json`, paper17 `THRESHOLD-EVIDENCE.json`,
`THRESHOLD-NATIVE-RECEIPT.json`, `THRESHOLD-RESOLUTION-2026-11-21.md`, `THRESHOLD-FINAL-PINS.json`, this
directory (`superseded-sources/` holds the pre-round editions of all fifteen threshold modules,
`failed-editions/` the two intermediate failures).

Not done: no independent final review (owner waiver); `reconcile_current_acceptance.py` not rerun;
`AGENTS.md` not edited. Earlier rounds' work is still uncommitted.

Lesson: a resident-memory stop with many seconds of CPU and large anonymous memory is elaboration. Here
`omega` with ordinal-valued subterms as atoms was the cause; abstracting the atoms into a separate
natural-number lemma removes it.
