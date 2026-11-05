# Accepted checkpoint: effective linear-name elimination

Client date: 4 November 2026. Acceptance receipt time: `2026-11-05T04:50:33.027462+00:00`.

This package continues `30af8ce523e32a8d26d2072642a152fd51314960` on
`formalization/cumulative-continuation-2026-11-04-second` with **twelve exact
frozen targets in three gates**. It closes elimination of any selected original
name that occurs only linearly in the existing restricted occurrence-row
grammar. Nonlinear terms at other names retain their original common valuation.

## Accepted result

For every source Boolean row formula `p`, selected name `i` passing the actual
linearity test, and original valuation `nu`, the concrete output satisfies

`(eliminate i p).eval nu <-> exists n : Nat, p.eval (update nu i n)`.

The linearity test checks every occurrence, including zero coefficients. The
algorithm handles arbitrary signed row coefficients, keeps the essential
coefficient-divisibility and natural-witness guards, and returns a formula in
the unchanged row grammar. Exact support removes precisely `i`. Original
guarded-atom meaningfulness and truth are retained under the same update.

The actual numeric linearity test, normalization, unit eliminator and full
eliminator are primitive recursive. Literal typed-code calibration has no
linearity premise. The executable program contains no valuation or semantic
oracle; fixed-valuation affine forms are used only to prove correctness by
the accepted Forests Presburger theorem.

| Exact gate | Targets | Result |
|---|---:|---|
| `LinearRowsSemanticStatementChecks` | 9 | Row arithmetic, split/test, positive moduli, normalization and actual elimination |
| `LinearRowsSupportStatementChecks` | 1 | Exact output support, including retained zero weights |
| `LinearRowsCodeStatementChecks` | 2 | Literal calibration and primitive recursiveness of the complete programs |

## Native verification and preservation

The focused aggregate `LogicLineages.ExternalCheckpoint20261104LinearRows`
passed. All **226 local source modules** in its import closure match
successful native receipts for their current source hashes. All twelve frozen
aliases passed the standard-axiom audit: only `propext`, `Classical.choice`
and `Quot.sound` occur.

The three definition/target files passed target-only preflight before proof
authorship and remain unchanged. The preceding 200-module plain-window closure,
all other preexisting Lean sources except appended public gate imports, and
the four newer PA addition-law files retain their accepted bytes. Dependency,
CI and manuscript configuration remain unchanged.

All native invocations used `scripts/check.py` with one worker, 2048 MiB heap,
1536 MiB process-tree RSS, 90 CPU seconds, 180 wall seconds per module and a
2048 MiB free-memory floor. Peak measured RSS across the archived receipts
was 1177216 KiB. The package archives 19 native receipts, including
12 failed preliminary attempts and their source hashes and raw logs;
the final accepted source versions all passed. The initial environment failure
was a missing official pinned Mathlib cache object, resolved by official cache
retrieval without upstream compilation.

The verification scope is this focused cumulative closure. No full public-root
rebuild or remote-CI result is claimed.

## Remaining source obligations

The whole source register remains **161 checked, 2 inherited, 26 pending / 189**.
There are no numbered source promotions. General nonlinear anchors, active-hyper
source-case assembly, general affine substitution inside nonlinear arguments,
dominant boundaries, exhaustive branch selection and the global decreasing
quantified-block induction remain pending. The full source normal-form,
elimination and first-order BASE decision endpoints and the separate PA
recursion endpoint remain pending.

Read the [source correspondence](SOURCE-CORRESPONDENCE.md),
[frozen statements](FROZEN-TARGETS.json), [acceptance record](ACCEPTANCE.json),
[source closure](SOURCE-CLOSURE.json), [raw compiler logs](COMPILER-LOGS.json),
[cache acquisition](CACHE-ACQUISITION.json) and
[metadata cross-check](METADATA-CHECK.json).
