# Original variable decoder realization: checked component

All four frozen exact contracts passed. The literal ternary Program checks the actual original `NumberedAuxiliaryDecoding.decodeVariable` success predicate using the actual `Encodable.encode Gamma`. It retains the nonempty guard, including rejection of a ground-type variable in the empty context.

- Native calibration: `OriginalVariableDecoderStatementChecks.native_exact`.
- Independent internal all-output nil rejection: `nil_exact`.
- Independent internal all-output cons-zero Boolean graph: `cons_zero_exact`.
- Independent internal exact cons-successor graph equivalence: `cons_successor_exact`.

The last theorem is original variable context-extension weakening: the same output and requested type remain, the new head code is arbitrary, and no finite-window membership premise is introduced. Every internal law is an actual `InternalCalculus.Derivation`, not reflection of native calibration.

## Verification

The coordinator ran all compilation with the unchanged serialized checker, 2048 MiB heap / 1536 MiB RSS, one thread, 180-second wall / 90-second CPU caps and 2048 MiB free-memory floor. No compiler or Git actions were run by the author or helper.

- Preflight: `1794400424071123409-5`.
- Native calibration: `1794400659879875217-5`.
- Independent equality/drop/checker support: `1794400781850702146-5`.
- Internal endpoints and four exact aliases: `1794400828639315858-5`.
- All 36 namespace-audited theorems and all four explicit exact aliases use only `propext`, `Classical.choice`, and `Quot.sound` (or a subset).

The three frozen source files still match `FROZEN-SHA256SUMS`. The reserved-identifier preflight correction is documented in `PREFLIGHT-REPAIR.md`; the attempted original specs and hash manifest were preserved before that repair. All accepted proof modules are immutable. The coordinator owns final source-matched import-closure evidence and publication; these focused gates are not a full-root or remote-CI pass.

## Scope

This is one concrete component of the ORIGINAL decoder, not a substitute relation or completion of a whole source theorem. No arbitrary opaque calibrated leaf inherits these internal laws. No existing selected `p`, global Package or SAME `OriginalLambdaTraversalSelection.finalData p` pipeline was changed.

The original variable-branch initial-witness integration is separate. Full constructor/list decoding, original source and primary representative transport, canonical internal cancellation and original I/C remain pending. The numbered register remains 171 checked, 2 inherited and 16 pending / 189; paper06 `lem:id1` remains pending.
