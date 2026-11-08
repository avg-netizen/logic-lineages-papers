# Parameterized result-stack composition validation

## Frozen statement and native gates

Independent static review accepted the three targets before proof authorship.
The reviewed manifest remains SHA-256
`fbf1bd922ae22712730114c6673828e230a7a0a3da10934e497fffd9db3dddc3`.
All 1,189 frozen/new and stable prerequisite pins match.

Comparator-only preflight passed before the proof files were authored:
`build-reports/1794154700228444818-6.json`
(SHA-256 `9d68c8e13615a8cc57efb799b6fb947e19083b8e79eeaeeab0224b57f2bd1277`).

The final exact gate is
`InternalParameterizedApplicationResultStackCompositionStatementChecks`:
`build-reports/1794155000693921931-5.json`
(SHA-256 `be33170ad8bab3b64feb246075bbcf21c6b1e4eddcefeff5e80dc66873996d9e`).

Its three aliases have exactly the frozen comparator types: RunZero,
WorkAppend and ResultSuffixFrame. Every alias's actual axiom closure is
`propext`, `Classical.choice`, `Quot.sound`. All 81 own-namespace audited
declarations, including aliases, pass that allowed-axiom policy. The exact
alias output is retained in `exact-checks.log`.

## Source-matched closure

The closure collector independently hashes all current local imports of
StatementChecks and Preflight. It finds 1,169 current source modules and
matches every one to a successful module row in 58 immutable numeric build
receipts. The 1,181 broader frozen Lean inputs also have successful
current-byte matches. The 17 new component source files are included.
No matching row is missing. `CLOSURE-SOURCE-PINS.json` is the portable source
hash map; detailed receipt/log/source maps remain local.

Only regular, non-symlink immutable numeric receipt files and matching logs
are used. Receipt and log hashes are recorded, memory-observation failures
are rejected, and every used receipt matches the unchanged resource profile.
Successful current-source rows from a partly failing invocation are usable;
the failed module itself is not. This is focused source-matched validation
with prior supplier receipts, not a fresh build of the complete import
closure or the whole project.

## Repairs and warnings

One FrameProof compilation failed because two `open` commands were combined
incorrectly. Its source snapshot and failed receipt remain local. Splitting
the commands fixed the parse error and all frame theorems then passed.
The initial induction-syntax proof passed with two unused simp-argument
warnings. Its snapshot was preserved and only the unused arguments removed.
The final source and all downstream proofs were rechecked successfully.
No current component warning remains. The 67 existing supplier warning
modules are unchanged and listed in local evidence. No `sorryAx`, new axiom,
unsafe proof shortcut or failed declaration is accepted.

## Resources and release

All seven owned checker sessions used `scripts/check.py`, one thread,
2048 MiB heap, 1536 MiB process-tree RSS, 2048 MiB minimum free memory,
90 CPU seconds, 180 wall seconds, and the pinned local upstream cache.
No upstream rebuild, dependency/configuration change or limit increase was
made. Peak successful component RSS was 1,160,696 KiB.
All owned sessions finished and both shared locks were verified free at
2026-11-08T16:24:00Z. No compiler remains owned by this component.

## Scope and publication

The proof preserves the actual state constructors, transition AST, raw
append AST, callback coordinate order and entire result stacks. The same
free parameter is carried through finite witness queries, substitutions,
renamings and internal induction. Terminal iteration is reused from the
accepted parameterized-stack prerequisite rather than added as a duplicate
target. No evaluation-extensionality or standard-model reflection argument
is used.

Preproof correspondence, manifest and static-check records remain untouched.
This validation and ACCEPTANCE describe their now-completed proof gates;
independent postproof review is still pending. No numbered source-register
change, full fold/fixed-fuel/canonical result, remote CI, Git action or
publication is claimed. The portable packet includes current sources and
hash-based evidence, not machine-specific compiler receipts, local logs,
attempt snapshots or orchestration files.
