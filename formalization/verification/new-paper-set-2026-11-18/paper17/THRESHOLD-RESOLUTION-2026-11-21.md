# Threshold route resolved (21 November 2026, local continuation)

This note supersedes the conclusion of `THRESHOLD-PARKED.md`; that note and everything under
`threshold-failures/` are left intact as history.

## Outcome

`LogicLineages.PermittedControl.StatementChecks.fixed_fullThreshold : Targets.FullThreshold` compiles
under the unchanged Mathlib profile (heap 2048 MiB, resident 1536 MiB, minimum free 2048 MiB). Final gate
receipt `1795231090968427178-2693071` (copy: `THRESHOLD-NATIVE-RECEIPT.json`). The read-only recursive
evidence verifier reports 290 source-matched modules, 0 errors, and standard axioms only
(`propext`, `Classical.choice`, `Quot.sound`) for the alias (`THRESHOLD-EVIDENCE.json`).

The six frozen pins of `THRESHOLD-FREEZE.json` were re-hashed before and after the work and all match:
the manuscript section, `ThresholdDefinitions.lean`, `ThresholdTargets.lean`,
`FixedEntryProgramDefinitions.lean`, `OrdinalEndpointCodeDefinitions.lean`, `OutputOffsetDefinitions.lean`.
No target, definition, checker, cap, heartbeat limit or manuscript was changed.

## What the stop was

The Guard stop was reproduced locally (receipt `1795230759039185265-2690829`): 16 s of CPU, about 0.81 GB
of anonymous memory (807,428 kB) on top of about 0.77 GB of loaded objects (767,156 kB). Unlike the paper 20 period stop this was
elaboration, not import footprint. The cause was `omega` being run with the actual ordinal-norm and tail
terms as its atoms; its atom table compares atoms up to definitional equality, which unfolds ordinal
arithmetic.

## What changed (proof modules only)

- `ThresholdGuardProof.lean`: the norm guard is now derived from a separate pure natural-number lemma
  `threshold_guard_arithmetic` in which every norm and tail is an abstract natural, and the left/right
  tail bounds are direct `le_max_left`/`le_max_right` terms. Statements of the four original theorems are
  unchanged. Peak resident memory 912,172 KiB; the largest module of the chain peaks at 1,072,460 KiB.
- `ThresholdEqualProof.lean`: one `rw … at` over five hypotheses replaced by `simp only … at` (the second
  equation does not occur in every hypothesis).
- `ThresholdBaseProof.lean`, `ThresholdTranslatedProof.lean`: `Part.mem_map_iff` takes its function
  explicitly; one equation in the equal-gap branch was stated in the wrong direction.

All other threshold modules compiled as drafted. Superseded and failed editions and all logs are in
`../../local-claude-continuation-2026-11-21-round3/`.

## Review status

Pre-scope review `THRESHOLD-PRE-SCOPE-REVIEW.md` approved the frozen comparator as the complete current
`prop:threshold` before any proof. No independent final review was run: the owner stated in the local
session that review is not necessary as long as the Lean compiles and the targets have not been changed.
Both conditions are recorded above.

## Limits

Focused closure only; no full-root or CI build. Correctness is on the proved computable tail for a
selected control with threshold, with all-input partial recursiveness and no claim of global totality.
This acceptance does not promote paper 17 `thm:arithmetic`, `thm:ground`, `thm:main` or the other pending
arithmetic lemmas.
