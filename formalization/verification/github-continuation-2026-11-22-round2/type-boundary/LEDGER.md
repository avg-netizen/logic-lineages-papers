# Type-boundary continuation ledger

## 2026-11-23 — source review and target proposal

Read #1453, #1461 and #1464 targets, corresponding round-3/round-4 source maps and annotations, and the original type algorithm, refit guard, scalar type checker and installed-tuple definitions at source head `b28541e6f1682fc41c47a385729df36e9db87b0d`.

No material mismatch in the accepted propositions. The internal type rules remain explicit premises; the narrower scalar is not a discharged instance of the actual source carrier. The round-4 handoff's short tuple summary should distinguish all valid type codes from types of accepted scalar addresses.

Proposed and root-approved continuation: prove the original numeric arrow law and explicit unbounded valid-code chain, refute the finite-window condition, and use the finite grammar membership conjunct to prove that a refitted checker can never satisfy `ActualTypeGuard` or occupy the corresponding `InstalledTupleAt` slot. This is stronger than #1464's calibrated implication and needs no type-guard calibration. A numeric arrow/domain/codomain counterexample records the precise obstruction to the guard-free route without claiming internal nonderivability.

All work is in new files. Root owns compiler, accepted records and Git. No accepted source, pin, policy, script or manuscript changes are authorized in this lane.

## Target freeze

Targets: `LogicLineages/PersistentMarking/NumberedWindowInternalCoverMeasuredApplicationTypeBoundaryTargets.lean`.

Source map: `verification/github-continuation-2026-11-22-round2/type-boundary/TYPE-BOUNDARY-SOURCE-MAP.md`.

Both files precede the proof module. Their SHA-256 values are recorded in the next entry before proof authoring.

### Frozen at 2026-11-23 03:57:08 UTC

The date above and this timestamp are UTC; the corresponding user-facing date is 22 November 2026 in America/Chicago.

- Targets SHA-256: `008bd58b1a5e86c4e1259e81555b3a498a579bddca9018cafbfcd95e3f719abc`.
- Source-map SHA-256: `e56a5f3b49934d02af47b0db8d6d2da1dada479b58a4bdd543caad595cfd2c5e`.
- Confirmed the proof module did not exist when these hashes were computed.
- Nine exact target propositions are frozen. No target edits will follow; any changed target must use a new name and preserve this version.

## Initial proof draft submitted to the root's native queue

Proof module: `LogicLineages.PersistentMarking.NumberedWindowInternalCoverMeasuredApplicationTypeBoundaryProof`.

Initial proof SHA-256: `a74b220dead1d717c7d99a68c3ec9735a7f04cc253cfa1182d5e480c4f63eeac`.

The proof supplies all nine frozen exact aliases and ends with their `#print axioms` commands. The original `typeTable` has its own earlier-cell lemma; the existing original-pair decoder round trip and component bound then give the numeric arrow equation. The explicit chain supplies a missing valid code above each finite list's maximum. Original scratch-membership evaluation rejects that code outside `s.types`, and the literal refit conjunctions propagate rejection. The installed-tuple conclusion projects its actual type-calibration conjunct.

Targets and source-map hashes rechecked unchanged. Native status: PENDING; no local compiler invocation, success claim, or accepted record. `NATIVE-REQUEST.json` names the module and exact endpoints. Any rejected draft will be preserved before repair.

## Additional frozen-map documentation erratum

Low severity, no target/proof defect: `verification/local-fable-pair-2026-11-22-round4/fable2/REFITTED-INSTALL-SOURCE-MAP.md:45` says `AcceptedTypesWindowed s` is assumed when its equivalence is used "left to right". The displayed and formal equivalence is `ActualScalarCalibration ... ↔ AcceptedTypesWindowed s`; the condition is consumed right-to-left and derived left-to-right.

Corrected wording for a linked review note: "AcceptedTypesWindowed is required to recover scalar calibration (right-to-left); conversely scalar calibration implies it." The old map and its pinned bytes remain unchanged, as do this packet's frozen targets and source map. Root was notified.

## Native failure and narrow repair

- Root receipt: `build-reports/1795407031709445528-11.json`.
- Log: `build-reports/1795407031709445528-11-LogicLineages-PersistentMarking-NumberedWindowInternalCoverMeasuredApplicationTypeBoundaryProof.log`.
- Targets compiled unchanged. The proof had one error at line 65: the table lookup rewrite could not find its expression inside the unreduced `match some (dom,cod)` produced by the accepted pair-decoder round trip. The reported downstream `sorryAx` dependencies are artifacts of this failed elaboration and are unaccepted.
- Before repair, preserved the entire initial proof with SHA-256 `a74b220dead1d717c7d99a68c3ec9735a7f04cc253cfa1182d5e480c4f63eeac`, its native request, and a failure note under `failed-drafts/1795407031709445528-11/`.
- Repair: split the rewrite and use an explicit definitional `change` to reduce the successful decoder match before applying the two table-lookup equalities. No target or source-map change, no extra hypothesis, no altered mathematical scope.
- Root rerun requested; status remains PENDING until the corrected proof passes its exact native/axiom gate.

## Final native success — authoring stopped

- Root gate04: PASS for all nine frozen exact aliases.
- Successful receipt: `build-reports/1795407134226655233-11.json`.
- Receipt SHA-256: `91340d52ffde04368a1155cac3b3e730a1f623543e01f3f618009e510de9b8a8`.
- Successful raw log: `build-reports/1795407134226655233-11-LogicLineages-PersistentMarking-NumberedWindowInternalCoverMeasuredApplicationTypeBoundaryProof.log`.
- Actual checked proof SHA-256: `3e88cbc09be1a72c7ed402445a0805c628870f5009b984a55627b2f27efc900e`.
- Frozen Targets SHA-256 remains `008bd58b1a5e86c4e1259e81555b3a498a579bddca9018cafbfcd95e3f719abc`.
- Frozen source-map SHA-256 remains `e56a5f3b49934d02af47b0db8d6d2da1dada479b58a4bdd543caad595cfd2c5e`.

The successful log reports exactly `[propext, Classical.choice, Quot.sound]` for each of `exact_TypeBitArrowLaw`, `exact_ValidArrowCodeChain`, `exact_ValidTypeCodesUnbounded`, `exact_FiniteTypeListOmission`, `exact_NoAllTypesWindowed`, `exact_RefittedValidTypeRejection`, `exact_ActualTypeRefitCounterexample`, `exact_RefittedTypeGuardNeverActual`, and `exact_RefittedInstalledTupleImpossible`. No `sorryAx` remains in the passing log. A harmless redundant-`rfl` linter warning is retained; no further proof cleanup or gate is needed.

`NATIVE-REQUEST.json` is marked complete with the successful receipt, exact named axiom output and final source hash. The initial failed draft and evidence remain preserved. Root is responsible for acceptance as supporting record #1475 and for packaging the raw receipt/log; this lane makes no register or Git edits.

The completed result is a numerical obstruction and an impossibility theorem about the accepted numeric installation predicate. It leaves internal codomain inversion, object-calculus nonderivability, application guard discharge, and the separate `AcceptedTypesWindowed` scalar question open. No further authoring is in progress in this lane.
