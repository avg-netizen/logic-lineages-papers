# Application existence ledger

## Targets frozen before proof

- Target: `LogicLineages/PersistentMarking/NumberedWindowInternalCoverMeasuredApplicationExistenceTargets.lean`
- SHA-256: `81806d2306efcea554d6062b5ed8244319763836ec7119e92c8e7b0f3dc5b398`
- Scope: `SOURCE-MAP.md`. No compiler run by this lane.

## Candidate ready for root gate

- Proof: `LogicLineages/PersistentMarking/NumberedWindowInternalCoverMeasuredApplicationExistenceProof.lean`
- Candidate SHA-256: `be60ab1d0bc5944aebad2ede21eca04df1ea7207eef94cb45038098c59c949a7`
- Exact endpoints: `exact_MeasuredApplicationExists`, `exact_MeasuredClassApplicationExists`.
- Native state: drafted, uncompiled; root owns the sole gate.

## Integration target frozen before proof

- Target: `LogicLineages/PersistentMarking/NumberedWindowInternalCoverMeasuredApplicationExistenceIntegrationTargets.lean`
- SHA-256: `6a5df992e326c4c23e0b905d628a41c82956a406c88290f8574ad5872466d696`
- Endpoint: `ExactInstalledCarrierApplicationExists`; see source-map integration section.

## Integrated candidate ready for root gate

- Proof: `LogicLineages/PersistentMarking/NumberedWindowInternalCoverMeasuredApplicationExistenceIntegrationProof.lean`
- Candidate SHA-256: `34cce115d6adfd24ac726de4580e9de6337300e5d88d8fbe70bf9a84b06a5635`
- Native state: drafted, uncompiled; root owns the sole gate.

## Native gates passed

The root's serialized native gates passed for all three exact endpoints.
This supersedes the earlier candidate-only native statuses above.

- Supporting record #1431: `exact_MeasuredApplicationExists` and
  `exact_MeasuredClassApplicationExists` passed in
  `build-reports/1795389808644602588-12.json`.
- Record #1431 evidence:
  `verification/github-continuation-2026-11-22/evidence/1431-p16-measured-application-existence-native.json`.
- Supporting record #1432: `exact_InstalledCarrierApplicationExists` passed in
  `build-reports/1795394451020498412-12.json`.
- Record #1432 evidence:
  `verification/github-continuation-2026-11-22/evidence/1432-p16-installed-carrier-application-existence-native.json`.
- The final successful integrated closure contains 3,712 local modules.
- Each of the three endpoint axiom closures contains only `propext`,
  `Classical.choice`, and `Quot.sound`.

A focused reread of both frozen target files against `SOURCE-MAP.md` found no
scope mismatch. The base common-least statement keeps the two function
matching windows, argument window, type guards and shared function least as
premises, while deriving both application least calls. The integrated
statement instead supplies operand windows from actual installed-scalar
acceptances and original same-context address reports; its type guards remain
explicit. Its conclusion is application `hasLeast`, not successful emission
of an accepted application-output address or a numbered paper completion.

No compiler or Git action was performed by this lane. Root packages and
records the native evidence. This update changes the ledger only.
