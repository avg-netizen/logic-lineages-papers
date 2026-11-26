# Combined conditional canonical and history evidence: PREPARED, NOT RUN

Coordinator-only invocation from formalization (no native compiler):

```sh
python verification/continuation-2026-11-13/conditional-canonical-and-history/run_evidence.py --run
```

Without --run the launcher only validates three configured tool/manifest hashes and prints arguments. It is portable relative to scripts/check.py; no workspace absolute paths are stored in CONFIG.json. DRY-RUN.json contains environment-resolved diagnostic arguments and is not the portable configuration.

Seven gates, thirteen exact aliases: ConstructorCongruence2, conditional C preservation1, CompatibleCancellation1, HistoryRunSplice5, HistoryLengthConservation2, ApplicationErase1, LambdaContextDeletion1. All current gate sources have successful source-matched native rows inventoried in NATIVE-GATE-READINESS.json; this inventory is NOT full artifact/evidence verification. Readiness receipts can be later successful reuse of already accepted sources. The configured closure currently contains 5,338 local modules.

The union manifest retains 227 frozen files from 90 relevant current continuation manifests. All seven direct packet manifests are included in full, including canonical preservation's custom INDUCTION-FROZEN-SHA256SUMS. Additional manifests are included in full when they freeze a dependency in this closure; FROZEN-PROVENANCE.json records every origin. Conflicting expected hashes fail preparation; every current union hash was matched read-only. Native checker is unchanged. Inherited checks use baseline 0dca825a0540a7608a276e377de7fef66c08bead and only formalization/AGENTS.md as allowed mutable inherited path, matching the prior accepted combined snapshot. Full inherited checks will rerun, not reuse stale results.

The launcher loads the exact adopted hardened-v2 verifier SHA recorded in CONFIG.json, changes only output HERE to this packet, and runs its unchanged checks. Tool/checker/frozen manifest hashes are checked before execution. No compiler, Git mutation, evidence pass or remote publication occurred during preparation. Coordinator must reserve a serial evidence window. Generated reports retain the verifier's candidate wording; adoption of the tool is separately recorded in bounded-evidence-verifier/COORDINATOR-ADOPTION.md, not mathematical adoption of this unrun packet.

## Scope limits

Constructor/C preservation and compatible Object cancellation retain explicit UniformRetainedCompatibility. It has NOT been established for the original retained representative. No unconditional cancellation or paper06 promotion follows. History splice/conservation preserve their actual installed literal-kernel/list/state scopes; no full HB claim. Supporting ApplicationErase/LambdaContextDeletion are included without changing their frozen endpoints. Numbered register remains unchanged.
