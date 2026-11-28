# Gate results for the coordinator's pending drafts (root lane, 27 November 2026)

Sources untouched. One gate call per row; `compiled` counts modules compiled in that call (the rest were cache hits).

| Gate log (`logs/`) | Receipt | rc | compiled | failed module | sorryAx in log |
| --- | --- | --- | --- | --- | --- |
| `codex-pending-NumberedWindowInternalLiteralBetaBoundIndexProof.txt` | `1795774421553402147-925530` | 1 | 0 | `NumberedWindowInternalLiteralBetaBoundIndexProof` | no |
| `codex-pending-NumberedWindowInternalLiteralBetaLeafSyntaxSupplierProof.txt` | `1795774428885987814-925565` | 0 | 3 | — | no |
| `codex-pending-NumberedWindowInternalLiteralJoinedLambdaChildWindowProof.txt` | `1795774261323482752-924578` | 0 | 20 | — | no |
| `codex-pending-NumberedWindowInternalLiteralLambdaPrefixContextIntroProof.txt` | `1795774346037880714-925147` | 0 | 1 | — | no |
| `codex-pending-NumberedWindowInternalLiteralLambdaPrefixHopProjectionProof.txt` | `1795774356019047836-925219` | 0 | 9 | — | no |
| `codex-pending-NumberedWindowInternalLiteralLambdaPrefixParentStopProof.txt` | `1795774305424481050-924864` | 0 | 15 | — | no |
| `codex-pending-NumberedWindowInternalLiteralSingletonLambdaBoundHitAcceptedProof.txt` | `1795774386685414692-925374` | 0 | 5 | — | no |
| `codex-pending-NumberedWindowInternalLiteralSingletonLambdaBoundOrderAcceptedProof.txt` | `1795774405310131689-925443` | 0 | 4 | — | no |
| `codex-pending-NumberedWindowOriginalFixedSeedCoverageProof.txt` | `1795774251261511990-924473` | 0 | 3 | — | no |
| `codex-pending-NumberedWindowOriginalFixedSettingsProof.txt` | `1795774254417650251-924529` | 0 | 1 | — | no |
| `codex-pending-Paper16AccessibilityMilestoneBetaAddressProof.txt` | `1795774458041833190-925702` | 1 | 0 | `NumberedWindowInternalLiteralJoinedBetaOutcomeProof` | YES |
| `codex-pending-Paper16AccessibilityMilestoneBetaLambdaConsumerProof.txt` | `1795774469418345162-925737` | 1 | 0 | `NumberedWindowInternalLiteralJoinedBetaOutcomeProof` | YES |
| `codex-window-ArrowTypedIntroductionV2+RetypedGroundV2.txt` | `1795773831011891982-921759` | 0 | 2 | — | no |
| `codex-window-DirectWindowSelectionV2.txt` | `1795774182715412200-924040` | 0 | 1 | — | no |
| `codex-window-GroundWindowTypingV2+RetypedJoinedWindowV2.txt` | `1795774162174855745-923903` | 1 | 1 | `NumberedWindowInternalLiteralJoinedBetaOutcomeProof` | YES |
| `codex-window-InstalledLambdaWindowV2.txt` | `1795773845162210392-921826` | 1 | 155 | `NumberedWindowInternalLiteralJoinedBetaOutcomeProof` | YES |

`sorryAx` appears only in the logs of failed calls (Lean prints it for the declarations after the error).
Every passed root's axiom report lists `propext`, `Classical.choice`, `Quot.sound` or a subset.

## Two drafts fail, each on a one-line defect; both repairs verified on renamed copies

1. `LogicLineages/PersistentMarking/NumberedWindowInternalLiteralJoinedBetaOutcomeProof.lean` (tracked, with the
   coordinator's uncommitted edit). Line 89 uses `eqn`; line 18 opens only `eqnRelabel sucRelabel zRelabel`.
   Repair: `open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel sucRelabel zRelabel)`.
   Verified copy: `…JoinedBetaOutcomeRepairCheckProof`, receipt `1795774225006756154-924321`.
   This one file blocks `Paper16AccessibilityMilestoneInstalledLambdaWindowV2`, `…GroundWindowTypingV2`,
   `…RetypedJoinedWindowV2`, `…BetaAddressProof`, `…BetaLambdaConsumerProof` (none reached their own source).
2. `LogicLineages/PersistentMarking/NumberedWindowInternalLiteralBetaBoundIndexProof.lean` (untracked draft).
   `private theorem consCongr` / `indexCongr` return a `Derivation`, which is data, not a proposition.
   Repair: `private def` for both. Verified copy: `…BetaBoundIndexRepairCheckProof`, receipt
   `1795774494332507116-925952`.

The originals were not edited (coordinator's uncommitted work). The `…RepairCheckProof` copies exist only to
prove the repairs sufficient; nothing imports them.

## After the `eqn` repair was applied to the original (04:18, see root ledger)

| Root | Receipt | Result |
| --- | --- | --- |
| `Paper16AccessibilityMilestoneInstalledLambdaWindowV2` | `1795774571363926080-926371` | PASS (51 modules compiled) |
| `…GroundWindowTypingV2`, `…RetypedJoinedWindowV2` | `1795774711062968825-927238` | PASS |
| `…BetaAddressProof` | `1795774722798565966-927293` | PASS (29 modules compiled) |
| `…BetaLambdaConsumerProof` | `1795774789827859632-927638` | FAIL: lines 47 and 65, `Formula α` resolves to `FirstOrder.Language.Formula` |

3. `LogicLineages/NativeModule/PersistentMarking/Paper16AccessibilityMilestoneBetaLambdaConsumerProof.lean`
   (untracked draft). The header does not open `ID1Completion.InternalCalculus`, so `Formula` is the
   first-order one. Repair: add `open ID1Completion.InternalCalculus`. Verified copy:
   `…BetaLambdaConsumerRepairCheckProof`, receipt `1795774934502289421-928551`
   (`exact_OpenInstalledAlignedBetaLambdaComputability`, standard axioms). Original not edited.

Only repair 1 was applied to an original, because a lane of this round needed its dependents. Repairs 2
and 3 are for the coordinator or owner to apply; the three `…RepairCheckProof` copies can then be archived.
