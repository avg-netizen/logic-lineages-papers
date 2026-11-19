# Paper19 exact decision equivalence at the original tree-code interface

Source: `19-source-expressivity-and-control-sensitivity/sections/observers.tex`
37–51 (entire original all-ground-free-variable domain, arbitrary result
types, both modes). The DAG importer `CurrentTreeInputCoverage` is a
supporting result, not the numbered decision endpoint. This plan connects it
to the exact current decision map without changing that map or its eight
frozen pins.

* Raw input is the existing `Source.OriginalInput.Query`: arity, strictness,
  and the two literal radix-eight encodings of original source trees.
  Check/convert both terms with the literal `CurrentTreeInputCoverage.compile`
  at the same replicate-zero type-code context of that arity. Return
  `none` when either check rejects. Otherwise pass the same strictness flag
  and both resulting raw DAGs to `CurrentDecision.toArithmetic p f`.
  Map the real `CurrentCompiler.compile` over that answer for the two
  literal ground comparisons. This is a total numerical algorithm with an
  option result, not a decision oracle. It performs no trusted decoding
  or selected-value lookup. Only the admitted terms get semantic meaning.
* An independent typed `OriginalUniversal` predicate evaluates literal
  `OriginalTerm` inputs, not DAGs by definition. It uses the selected
  policy's actual `AdmissibleAssignment.assignment` and the current
  `CurrentCounterBound.compareAt f strict` of those vectors at every
  positive valuation in the ground-only context. This is the typed
  predicate quantified by `CurrentCounterBound.Good`; its source
  independently confirms the mode/positive-coordinate convention. The
  witness valuation correspondence with `ExistentialPlan.inputs ρ + 1`
  is literal: every ordinal component at a ground-only context has a
  ground variable; its index is the unique `Fin 1` value. Pick
  `ρ x := ν ⟨Ty.ground,x,0⟩ - 1` when going back from a positive valuation.
* For every arity, strictness, arbitrary two result types, and two
  literal original terms in that context, retain separately: (1) both
  admitted original codes are transformed to the exact raw DAG codes
  of their actual typed terms; (2) the literal result is
  `some (n+6, encodeInput r)`; (3) typed `OriginalUniversal` is equivalent
  to unsatisfiability of that very r; (4) the composed ground-output
  construction emits `some (CurrentCompiler.expected r)`, with the exact
  typed strict and weak comparison semantics already paid by
  `CurrentDecisionTargets.ArithmeticReduction`. For ground-typed t,u
  the original relation is the ordinary selected-policy ground scalar
  criterion with no new assumption.
* All raw queries: exact rejection iff one of the two literal type
  checks yields none. Computability of both actual raw option maps
  assumes only the manuscript's computable selected policy, computable
  permitted f, and established `CurrentDecisionTargets.Effective`.
  Preserve raw malformed independent of typed correctness. No claim of
  deciding the relation or of feasible magnitude of closed anchors.

Proof dependencies after their separate gates: `ActualTreeCodes` supplies
literal encoding and (input t).term = t, then `GeneralReduction` gives the
checked final arithmetic query; `ArithmeticReduction` gives actual strict
and weak outputs in their fresh shared existential ground contexts.
`GroundSpecialization` identifies direct ground source comparison. Effectivity
is option sequencing/composition from `ActualRawProgram` and `Effective`,
never from existence of typed targets alone. If accepted as a companion
leaf, freeze fresh definitions/targets and exact source comparator before
native preflight and proof. This plan does not edit or weaken any frozen
target and does not claim a completed proof.
