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
