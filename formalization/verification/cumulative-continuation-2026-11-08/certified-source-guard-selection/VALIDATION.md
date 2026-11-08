# Validation: certified source-guard selection

## Exact checks

The independently reviewed frozen Definitions, Targets and Preflight passed
before proof authorship in immutable receipt
`build-reports/1794136659194410399-9.json`. The original preflight log is
`../internal-representative-congruence/certified-source-guard-preflight.log`.
A local copy of the immutable receipt is retained here.

All four authored proof files passed on their first native check in immutable
receipt `build-reports/1794137181147255975-7.json`; the log is `exact-01.log`.
The source snapshot in `candidates/attempt01/` is the successful candidate.
No frozen file, supplier, target, compiler option or resource limit changed.
There were no failed native proof attempts for this component.

The exact aliases are:

- `certified_source_guard_calibration_exact`.
- `certified_step_factorization_exact`.
- `certified_typed_factorization_exact`.
- `certified_source_guard_selection_exact`.

The support namespace audits four internal graph derivations, the evaluation
namespace audits eleven external calibration/existence lemmas, the main proof
namespace audits four frozen target proofs, and the exact checks namespace
audits four aliases. All 23 actual theorem closures use only `propext`,
`Classical.choice` and `Quot.sound`.

## Source-matched closure and resources

The focused exact-gate/preflight import closure contains 1,159 local modules,
including meta imports. Every current source SHA256 matches a successful row
in one of 57 immutable numeric receipts. Matching prior supplier receipts are
reused. This is not a fresh build of every closure module or the full project.
`SOURCE-PINS.json` records all closure source hashes; the local
`closure-receipts.local.json` records successful receipt, source and log hashes.
All 61 frozen/prerequisite/manuscript/correspondence pins match exactly.
The collector excludes mutable latest aliases, symlinks and nonnumeric receipt
names and checks both printed exact-alias axioms and namespace audits.

The unchanged profile was 2,048 MiB heap, 1,536 MiB process-tree RSS cap,
2,048 MiB minimum free memory, one thread, 90 CPU seconds and 180 wall seconds.
Peak successful component RSS was 1,068,836 KiB. The maximum across reused
successful closure receipts was 1,176,760 KiB. The pinned upstream cache was
used; no upstream rebuild, dependency change or resource increase occurred.

The only owned compiler session exited with code zero. Both shared locks were
observed free before release to the parent coordinator; see `slot-release.json`.
Post-checkpoint review and publication remain the coordinator's responsibility.

## Claim boundary

The raw-target source-validity step guard is redundant on original accepted
steps only under subtype closure. The actual target representative retains
packed decoding, without a universe filter. The typed fixed-point test is
redundant because original canonical acceptance supplies the actual original
representative equality and the same N is externally calibrated to it.

The internal factors retain the actual H and N graphs. External calibration
is not reflected into internal proof. This component does not prove lifted
step acceptance, internal representative application congruence, combined
quotient-edge compatibility, path preservation, joint-context uniformity,
bad-window fallback, CertifiedApplicationLift or all-term accessibility.
The source register is unchanged. No full-root, remote-CI or Git claim.
