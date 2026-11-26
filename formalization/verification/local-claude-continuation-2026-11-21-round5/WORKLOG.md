# Worklog — local Claude root, fifth round, 21 November 2026 (UTC)

Owner instruction: "Please continue" (after the round-four report, which recommended the Paper 17
arithmetic lemmas and asked whether new targets should be reviewed). Single lane; compiler only through
`scripts/check.py` with the unchanged Mathlib profile. Nothing committed or pushed.

- Read `17-…/sections/arithmetic.tex` in full. None of `thm:arithmetic`, `lem:field-comparison`,
  `lem:count-transfer`, `lem:inner-termination` had a target, plan or draft.
- Chose `lem:inner-termination`: its claim is about the charge only and needs no field semantics.
- Wrote `InnerTerminationTargets.lean` (rows, 𝓜, 𝓥, dispositions, `ZeroClassReplacement`,
  `FullInnerTermination`). Gate `logs/targets-01.log` failed (two definitions needed `noncomputable`;
  edition kept in `failed-editions/`); `logs/targets-02.log` pass. Froze two pins in
  `paper17/INNER-TERMINATION-FREEZE.json` before any proof.
- `InnerTerminationProof.lean`: arithmetic over abstract naturals, sum-over-union bounds, per-member
  weight bound, main lemma. `logs/proof-01.log` failed on one misapplied `Nat.pow_succ` (edition kept);
  `logs/proof-02.log` pass.
- `InnerTerminationStatementChecks.lean`, gate `logs/full-01.log`: pass, receipt
  1795237985721802859-2723078. Recursive evidence: 3 modules, 0 errors, standard axioms only
  (`logs/inner-termination-root-verify.log`). Freeze pins re-hashed: match.
- Record 702 written; register entry set to checked; counts 154 / 13; STATUS.md updated.

No independent review of the new target; the record and STATUS.md say so, and also that the target is
Claude-authored where the register's acceptance line names a Codex-owned comparator.

New files: three `InnerTermination*.lean` modules, `accepted/702-inner-termination.json`, paper17
`INNER-TERMINATION-{FREEZE,SOURCE-MAP,EVIDENCE,NATIVE-RECEIPT,FINAL-PINS}`, this directory. Tracked files
changed: `CURRENT-COMPARISON-TARGETS.json`, `verification/new-paper-set-2026-11-18/STATUS.md`.

## Second statement of the round: `lem:count-transfer` (record 703)

- Read the supplier targets: `EntryExistenceOrbit`, `IdentityEntry`, `ActualAffordableCocycle`,
  `GapInputComparison`, `ActualInverseTable`, `EqualGapCertificateEffective`. Found that the exact count
  formula behind (count-core) existed only inside the proof of `long_entry_state` (funnel branch), which
  states a residue.
- Wrote `CountTransferTargets.lean` (`countCoreConstant`, `CountCore`, `ZeroClassExact`,
  `EqualInputMerge`, `DistinctInputGap`, `RankTransfer`, `FullCountTransfer`). Gate
  `logs/ct-targets-01.log`: pass. Froze seven pins in `paper17/COUNT-TRANSFER-FREEZE.json` before proof.
- `CountTransferCoreProof.lean` (`funnel_exit`, `countCore`; arithmetic over abstract naturals): pass on
  the first gate, `logs/ct-core-01.log`; two warnings tidied afterwards (deprecated lemma name, unused
  binder) and re-gated inside `logs/ct-proof-01.log`.
- `CountTransferProof.lean` (zero class, merge, gap, rank transfer, conjunction): pass on the first gate,
  `logs/ct-proof-01.log`.
- `CountTransferStatementChecks.lean`, gate `logs/ct-full-01.log`: pass, receipt
  1795238683060030166-2724820. Recursive evidence: 266 modules, 0 errors, standard axioms only
  (`logs/count-transfer-root-verify.log`). Freeze pins re-hashed: match.
- Record 703 written; register entry set to checked; counts 155 / 12; STATUS.md updated.

No independent review of this target either; recorded as for 702.

Further new files: four `CountTransfer*.lean` modules, `accepted/703-count-transfer.json`, paper17
`COUNT-TRANSFER-{FREEZE,SOURCE-MAP,EVIDENCE,NATIVE-RECEIPT,FINAL-PINS}`.

## Third statement of the round: `lem:field-comparison` (in progress)

- Wrote `FieldComparisonTargets.lean`: field syntax (`iterate`, `entry`), actual values, forms, the
  computable normalizers `distinctForm` and `sameForm`, and five clauses. Gate `logs/fc-targets-01.log`:
  pass (both normalizers compile as computable definitions). Froze nine pins in
  `paper17/FIELD-COMPARISON-FREEZE.json` before proof.
- `FieldComparisonPeelProof.lean` (comparison and row lemmas under strictly increasing maps, notation of
  ω·c, `long_peel_bound`, `entry_peel`): pass on the first gate, `logs/fc-peel-01.log`.
- `FieldComparisonProof.lean` (normalizer case lemmas, four distinct-input cases, four equal-input cases,
  short entries, uniqueness, well-formedness): `logs/fc-proof-01.log` failed on one rewrite that hit the
  wrong iterate (edition kept in `failed-editions/`); `logs/fc-proof-02.log` pass.
- `FieldComparisonStatementChecks.lean`, gate `logs/fc-full-01.log`: pass, receipt
  1795239476384903099-2726545. Recursive evidence: 278 modules, 0 errors, standard axioms only
  (`logs/field-comparison-root-verify.log`). Freeze pins re-hashed: match.
- Record 704 written; register entry set to checked; counts 156 / 11; STATUS.md updated.

No independent review of this target; the record lists its modelling limits (long intervals only,
existential tail, no primitive-recursion theorem for the normalizer).

Further new files: four `FieldComparison*.lean` modules, `accepted/704-field-comparison.json`, paper17
`FIELD-COMPARISON-{FREEZE,SOURCE-MAP,EVIDENCE,NATIVE-RECEIPT,FINAL-PINS}`.

## End of round

Register 156 checked / 11 pending (Paper 17 at 30 of 33). Remaining: Paper 16 `thm:main`,
`lem:structural-interpretation`, `lem:arithmetic-accessibility`, `thm:upper`, `lem:realization`,
`thm:iteration`, `lem:tower-cofinality`, `thm:height`; Paper 17 `thm:main`, `thm:arithmetic`, `thm:ground`.
Policy re-paused. Nothing committed or pushed. `reconcile_current_acceptance.py` not rerun; `AGENTS.md`
not edited.
