# Bounded result fold: validation and consumer API

The six unchanged propositions in
`InternalApplicationResultFoldCalibrationTargets` are proved. The exact
gate is `InternalApplicationResultFoldCalibrationStatementChecks`.

## Consumer declarations

- `InternalApplicationResultFoldCalibrationMeaningProof.actualOriginalSemanticResultFoldEquation`
  gives the all-input equation of the independent semantic fold.
- `InternalApplicationResultFoldCalibrationExecutionProof.actualOriginalEncodedResultStackIteration`
  identifies the complete original numeric iteration with encoded structured
  execution for every count and state, including malformed configurations.
- `InternalApplicationResultFoldCalibrationExecutionProof.actualOriginalResultStackSufficientFuel`
  gives sufficient work-weight fuel for live states, one extra step for any
  status, and preservation of terminal states at every further count.
- `InternalApplicationResultFoldCalibrationMeaningProof.actualOriginalResultStackMeaningInvariant`
  preserves the exact work/result denotation by one transition and iteration.
- `InternalApplicationResultFoldCalibrationCompletionProof.actualOriginalCompletedResultFold`
  finishes one visit with any background result stack at any count at least
  the original `2 * payload + 1` budget, preserving that background literally.
- `InternalApplicationResultFoldCalibrationEvaluationProof.actualOriginalBoundedResultFoldCalibration`
  proves both the exact encoded singleton output state of the actual bounded
  run and the all-input value of the actual fold program.

All three input programs are arbitrary. The guard and leaf have arity one;
combine has arity four with the literal domain, codomain, function-result,
argument-result ordering. There are no validity, calibration, result tag,
representative, output-size or internal-derivability premises.

## Independent semantics and proof route

`semanticFold` is genuine well-founded recursion on the original term
payload. Its definition contains no transition, run, iterator or fuel. The
accepted original application payload bound proves both recursive children
smaller even when the reconstructed arrow type or computed values grow.

The finite-list `workMeaning` definition is structurally recursive on the
pending worklist. It resolves a visit directly by the independent semantic
fold; it never expands a visit or constructs machine work. A finish consumes
two results in the stack's argument-first order and calls combine in the
original function-first order. Unknown frame tags, finish underflow and
non-one status denote failure.

The recursion equation proves the opening case of one-step denotation
preservation. The leaf, finish, malformed and terminal cases are exact
structural equations. Iteration preserves this denotation. Separately, the
checked strict work decrease proves sufficient fuel to reach canonical
failure or empty live work. The initial visit has a successful singleton
denotation, excluding failure; hence its terminal state contains exactly
the semantic value and original background results. Existing program
evaluation equations then calibrate the original bounded run and selector.

The completion theorem deliberately has no work suffix. Terminal padding
can start an appended work suffix early. It preserves arbitrary result
backgrounds without asserting a false intermediate-state framing law.

These are external natural-number semantic results. They do not reflect
truth into the original arithmetic calculus, establish internal recursive
constructor closure or prove any original representative property.

## Checks and reproduction

The exact gate has six aliases; four proof modules have 24 other audited
theorem entries. All actual axiom closures are contained in `propext`,
`Classical.choice` and `Quot.sound`. Independent static specification review
and native preflight preceded proof author admission. The frozen definitions,
targets, preflight, correspondence and selected original suppliers are
unchanged, with 40 comparisons including the original manuscript.

The local import closure, including public meta imports, contains 837
source-matched modules. Every source hash has a successful immutable native
receipt. Earlier matching supplier receipts are reused; there is no fresh
whole-closure, full-root or remote-CI claim. The local evidence collector
excludes mutable receipt aliases and symlinks.

An initial invocation stopped before launching Lean because the runtime
environment had not been sourced. After using the established environment,
the execution module passed; the first meaning proof exposed only a
dependent-if/ordinary-if simplification gap. A two-branch proof repair closed
that gap without changing the frozen semantic definition or any target.
The subsequent exact gate and all audits passed. Failure bytes, logs and
immutable row-by-row receipt mappings remain local.

The unchanged profile is one thread, 2048 MiB heap, 1536 MiB RSS, a 2048 MiB
free-memory floor, 90-second CPU and 180-second wall limits, with pinned
upstream caches only. Peak component RSS was 1,044,840 KiB; the inherited
source-matched closure receipts peak at 1,176,760 KiB. The toolchain is
Lean v4.32.0-rc1.

Reproduce with the pinned toolchain/cache available, from `formalization`:

```
python3 scripts/check.py --memory-mib 2048 --rss-mib 1536 --min-free-mib 2048 --threads 1 --cpu-seconds 90 --timeout 180 LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultFoldCalibrationStatementChecks
```

No numbered source statement changes status. Original representative-specific
calibration, internal composition/constructor closure and the remaining
paper06 accessibility dependencies are separate obligations.
