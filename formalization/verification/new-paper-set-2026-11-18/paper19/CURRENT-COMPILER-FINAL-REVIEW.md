# Independent final review: paper19 thm:compiler (root, local continuation)

Accepted as the current numbered statement `thm:compiler` (compiler.tex
127–133). Reviewer: root of the local three-party continuation, not the lane B
author. No reviewer native run.

## Comparator against the printed statement

`CurrentCompilerTargets.CompleteCompiler` is a seven-part conjunction.

- "computably constructed": `Effective` gives Computable for the checked
  Option routine `run` and for the total `compile`, on all natural inputs.
  `LiteralOutputs` identifies the computed codes with the encoded strict and
  weak comparison pairs of the typed Boolean compiler, for every shared
  interleaved input and for every explicit existential-prefix sentence of the
  source AST. `ValidCodes` reconstructs a typed input from every raw success
  and makes rejection an iff with absence of a typed preimage. Outside that
  domain `compile` returns two fixed closed zero pairs; no semantic claim is
  made there.
- "true precisely when the sentence is false": `ASTCorrect` and
  `SharedCorrect` state, for every control satisfying the printed source-growth
  inequalities and every parsing policy, that the strict comparison holds iff
  the sentence does not, and likewise the weak comparison. Universality over
  valuations is inside `Strict`/`Weak`; the shared form is normalized
  directly, never through tree expansion.
- "all free variables ground; shared inputs and source leaves retain their
  valuations": `Retention` gives, for every original valuation, an iff with a
  forest valuation that agrees with it on every embedded original coordinate,
  and an all-ground output context.
- "polynomial added size": `OutputBudgets` bounds the four actual output table
  lengths by 10000*(cost+1)*(sourceMax+1)+7 for sentences and
  10000*cost*(sourceMax+1)+7 for shared inputs, an explicit polynomial in the
  formula budget and supplied source tables, with the AST occurrence measure
  kept distinct from the shared-DAG budget.

No hypothesis beyond the printed growth condition on the control is added; no
decider, witness or successful-compilation premise appears.

## Evidence

Gate receipt 1795035096239476837-16. Nine frozen pins recomputed and match.
Compiler-free recursive evidence reproduced independently and JSON-identical
to the author's CURRENT-COMPILER-EVIDENCE.json: 458 source-matched modules,
zero errors; the exact alias
`CurrentCompiler.StatementChecks.fixed_complete_compiler` and every other
audited declaration in the closure depend only on propext, Classical.choice
and Quot.sound. No unsafe, opaque, implemented_by, extern, partial, axiom,
sorry or native_decide in the ControlSensitivityCurrent files of the closure.
Supporting packets 381, 382 and 384–391 cover the raw codec layers.

## Limits

This is the compiler theorem only. `cor:ground-equivalence`,
`thm:control-hardness` and the later paper19 statements remain pending. The
semantic definitions of sentence truth and of the strict/weak comparisons are
the previously frozen ones and were not re-derived in this review. No
full-root or CI claim.
