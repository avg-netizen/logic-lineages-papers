# Original representative fold: checked external calibration

All three unchanged frozen targets are proved and pass their exact aliases
in `InternalRepresentativeFoldCalibrationStatementChecks`.

## Consumer declarations

- `InternalRepresentativeFoldCalibrationSemanticProof.actualOriginalSemanticRepresentativeFoldCalibration`
  equates the independent original-payload semantic fold with the original
  packed-target representative for every natural input, under subtype closure.
- `InternalRepresentativeFoldCalibrationProof.actualOriginalRepresentativeFoldProgramCalibration`
  gives the full original `InternalQuotientEdgeChecker.Calibrated` contract
  for the concrete `foldedData`, including the unchanged step program and
  both all-input source/target representative equations.
- `InternalRepresentativeFoldCalibrationProof.actualOriginalFixedWindowRepresentativeSelection`
  selects exactly that Data for a subtype-closed fixed window and exactly
  the old Data for every other window. This is an existential result, not a
  uniform compiler.

The frozen concrete ASTs are in `InternalRepresentativeFoldCalibration`:
`rootGuard`, `leaf`, `combine`, `normalizer`, and `foldedData`. Later internal
constructor proofs must reuse those exact definitions. The root guard is
recursive source validity on the whole original input; combine explicitly
pairs the original codomain with the old target representative's payload.

## Source argument and fallback behavior

The support proof first reuses checked recursive-validity and target-tag
wrapper calibration. For a source-valid application root, it obtains an
original universe decode. The exact constructor tag eliminates all other
term constructors. Both original children are therefore typed and in the
universe. The original decoded-representative supplier then gives equally
typed universe representatives for each child. The original representative
application congruence is applied with its explicit subtype-closure and
four universe premises. Original packed decoding and representative outer-
type preservation justify the combine's syntactic codomain repacking.

Strong induction is on the original input payload only. The accepted
application payload bound makes both recursive children smaller. Neither
reconstructed packed codes nor computed outputs are assumed to decrease or
fit a bound. Rejected roots and nonapplications use the checked leaf on the
whole unchanged raw input. This retains the original behavior for packed
targets outside the universe and for malformed inputs, without a stronger
target decoder or a target-universe condition.

The concrete program theorem consumes the checked generic bounded-result-
fold calibration as a theorem. No generic calibration premise is added.
The source projection uses the exact-one source test; accepted source and
packed target representatives agree by their original decoders, and rejected
sources return zero. The target projection remains the normalizer on every
input. Nonclosed windows retain all three old program fields literally.

## Checks and immutable receipts

Independent static specification review was accepted before proof authorship.
The unchanged three preflight modules passed in immutable receipt
`build-reports/1794135083641742181-5.json`.

The successful exact gate and all four new proof/check modules passed in
`build-reports/1794135409491672215-9.json`, copied to `exact-receipt.json`.
The gate has three exact aliases, and the support/semantic/program proofs
have thirteen other audited theorem entries. All actual axiom closures are
contained in `propext`, `Classical.choice`, and `Quot.sound`.

The first support candidate failed only because a rewrite did not expose
`applicationPacked` in an already-proved selector equality. That exact
candidate and immutable failed receipt are retained in
`failed-candidates/attempt-001/`. Explicitly simplifying that abbreviation
repaired the proof; all frozen statements and source semantics stayed fixed.
The successful program proof has one harmless unused-simp-argument warning.

The local import closure of the exact gate and comparator preflight contains
852 source-matched modules, including meta imports. `SOURCE-PINS.json` and
`closure-receipts.json` record current hashes and successful immutable receipt
rows for all of them. Existing matching supplier receipts are reused. This
is not a fresh 852-module build, full-root build or remote CI result.

All 68 frozen/specification/prerequisite/manuscript pins still match. The
component contains seven Lean files. Peak successful component process-tree
RSS was 1,045,060 KiB. The maximum among all reused successful closure receipts
was 1,176,760 KiB. Both are below the unchanged 1,536 MiB RSS cap.

The bounded profile was unchanged: heap 2,048 MiB, RSS 1,536 MiB, free-memory
floor 2,048 MiB, one thread, CPU 90 seconds, wall time 180 seconds, pinned
upstream cache only. The compiler process was reaped and the sole slot
released to the coordinator after the successful gate.

Reproduce from the `formalization` directory only with a fresh coordinator
compiler-slot grant. Use the installed pinned toolchain from `lean-toolchain`,
`leanprover/lean4:v4.32.0-rc1`, with its Lean and Lake executables on PATH and
the existing pinned dependency cache available. Do not rebuild upstream
dependencies or raise the resource limits.

    python3 scripts/check.py --memory-mib 2048 --rss-mib 1536 --min-free-mib 2048 --threads 1 --cpu-seconds 90 --timeout 180 LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeFoldCalibrationStatementChecks

## Remaining boundary

These are external standard-natural-number results. They do not supply an
internal graph witness, reflect evaluation truth into `Derivation`, or allow
program substitution based solely on external equality. Internal certified
fold constructor closure, representative application congruence, application
lifting, context-uniform integration and the all-term ID1 endpoint remain
separate. No numbered source status or global register was changed. No Git
operation, publication, full-root build or remote CI was performed.
