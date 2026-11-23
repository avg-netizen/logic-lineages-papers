# GitHub continuation — 22 November 2026, third round

**Numbered progress:** Paper 16 `thm:iteration` and `lem:realization` are now
checked, bringing the replacement register to **162 checked / 5 pending / 167**.
Every remaining numbered obligation is in Paper 16. No manuscript wording was
changed.

This continuation starts at `9a8fd8f8ffd9c1ab27b91096dc1e52aa196bb413` on
`formalization/github-measured-install-2026-11-22`. Fetch confirmed that base
before the work began. The user requested continued formalization, and the
existing commit/push authorization remains in force on that branch.

**Completed mathematical gates:** **14 new Lean files**, **23 new exact checked
aliases**, and six records **#1478–#1483**, comprising two numbered adoptions and
four supporting packets. The iteration adoption reuses its previously compiled
exact endpoint and source/evidence checks; it is not an additional new alias or
a redundant replay. The acceptance inventory, portable native evidence, frozen
source checks, and final queue/policy closeout are complete.

## Numbered adoptions

| Record | Statement | Basis |
| --- | --- | --- |
| [#1478](../new-paper-set-2026-11-18/accepted/1478-p16-thm-iteration.json) | Paper 16 `thm:iteration` | The actual native iterator realizes the printed full-prefix finite-type iteration, with successor composition and the full earlier orbit at nonzero limits. The independent source review confirms that its existing proof does not depend on the formerly missing structural lambda theorem. |
| [#1483](../new-paper-set-2026-11-18/accepted/1483-p16-lem-realization.json) | Paper 16 `lem:realization` | A separately frozen, natively proved conjunction combines the existing realization closures, the new structural typed-lambda theorem and its syntax/substitution bridges, and the existing finite-chain transport result. |

The iteration decision and reused evidence are documented in
[ITERATION-PROMOTION-REVIEW.md](ordinal-frontier/ITERATION-PROMOTION-REVIEW.md)
and [ITERATION-PROMOTION-CHECK.json](ordinal-frontier/ITERATION-PROMOTION-CHECK.json).
The realization conjunction is documented in
[REALIZATION-COMPLETION-SOURCE-MAP.md](root/REALIZATION-COMPLETION-SOURCE-MAP.md),
with independent source assessment in
[TYPED-LAMBDA-SOURCE-REVIEW.md](ordinal-frontier/TYPED-LAMBDA-SOURCE-REVIEW.md).

### What completes the lambda clause

The new intrinsic grammar has all four constructors of the simply typed
lambda/application fragment: typed variables, interpreted constants,
application, and abstraction. It permits arbitrary nested binders. Its types
are the existing finite semantic types, and its arrow values are all set
functions. Semantic base `ι` maps to actual native type `σ = o → o` through the
existing type translation.

The compiler uses the existing `Spine.Expr.bound`, `Spine.Expr.lam`, and native
application constructors. Closed native constant terms are inserted literally.
The checked syntax bridge establishes native typing/closedness and exact
compatibility with the actual de Bruijn substitution operation. In the
fundamental theorem, lambda-body realization follows by structural induction
under an extended realizing environment, followed by the checked beta-instance
equation and existing strict backward transport. It is not a supplied premise.

Realizing interpretations of constants and free variables are the ordinary
premises of the fundamental lemma. Its closed pure-lambda specialization has
neither premise. This is the full lambda fragment at the printed realizer
types; it is not a denotation theorem for arbitrary marked syntax or every raw
native T expression at untranslated ground types.

The complete comparator retains strict backward transport, semantic downward
closure, nonempty countable pointwise suprema, and finite-chain transport.
Backward transport goes from realization at the smaller target to realization
at the larger source, as used by the printed beta argument and rank definition.
The manuscript is unchanged.

## Supporting additions

| Record | Exact contribution | Current validation and boundary |
| --- | --- | --- |
| [#1479](../new-paper-set-2026-11-18/accepted/1479-p16-actual-omega-index-tower.json) | Eight exact endpoints for the actual ordinal index tower beginning `0, 1, Ω`, with `Ω = ω₁`: recurrence, strict increase, arguments below the endpoint, strict cofinality, least-fixed-point representation, fixedness, minimality, and their conjunction. | Native passed. This supplies actual index-order facts, not the coefficient norm, epsilon-index identification, intended collapse, Simmons calibration, or BH identification. |
| [#1480](../new-paper-set-2026-11-18/accepted/1480-p16-structural-lambda-fundamental.json) | Seven exact native typing, closed compilation, substitution, beta-instance, structural realization, pure closed realization, and combined-fragment endpoints. | Native passed; incorporated into numbered #1483 through its separately frozen conjunction. |
| [#1481](../new-paper-set-2026-11-18/accepted/1481-p16-internal-finite-type-membership.json) | Five exact internal finite-membership and program guard/image-transfer endpoints. | Native passed. Statements retain explicit finite numerical acceptance/image conditions and the original program calibrations. |
| [#1482](../new-paper-set-2026-11-18/accepted/1482-p16-internal-grammar-codomain.json) | Two exact internal grammar-codomain endpoints, including the existing `GrammarCodomainInversion` predicate. | Native passed. Both require the explicit finite numerical `FiniteCodomainClosure s.types` condition. |

### Actual ordinal indices

The new definitions use the actual first uncountable ordinal in Mathlib's
full ordinal type:

```text
Ω = ω₁
a₀ = 0
aₙ₊₁ = Ω^aₙ
Λ = supₙ aₙ
```

The proved endpoint is the least fixed point of `α ↦ Ω^α` above zero; every
pre-fixed point bounds it. Every finite argument lies strictly below the
endpoint, and every ordinal below it lies strictly below some argument.

The packet does not define epsilon notation to make the manuscript's
`Λ = ε_(Ω+1)` identity automatic. That literal epsilon bridge remains separate.
It also does not replace the hereditary coefficient norm by a constant or
instantiate a toy collapse as the intended Veblen-hull collapse. The exact scope
is recorded in [OMEGA-TOWER-SOURCE-MAP.md](ordinal-frontier/OMEGA-TOWER-SOURCE-MAP.md).

### Internal finite membership and grammar guards

The checked internal packet uses the original `scratchMember` program on the
standard literal encoding of a supplied finite list. Its exact equivalence
identifies membership of an arbitrary open candidate with the finite
disjunction of equalities to the listed numerals; the empty list gives falsity.
The guard and image-transfer constructions eliminate that finite disjunction,
use the original program's concrete numeral proofs in each branch, and
transport them by internal equality.

The frozen statements distinguish the following premises:

- Finite guard transfer requires the supplied original program to evaluate to
  one at every listed numeral and an internal proof of the candidate's literal
  membership.
- Finite image transfer requires each listed input's actual program value to
  belong to the output list, plus the actual open program graph and literal
  input membership.
- The actual-type instance retains `ActualTypeGuard TV` and validity of every
  code in the finite list. It preserves the supplied all-type program `TV`.
- The window/refit instance retains `TypeGuardCalibrated s T`,
  `GrammarTypeInclusion s`, validity of every window-list code, and explicit
  internal membership in that window list.
- Grammar codomain inversion requires `FiniteCodomainClosure s.types`: the
  actual `cellTail` value of **every** listed code belongs to the same list.
  It derives grammar membership of an open `cod` from grammar membership of
  `rawCons dom cod`; no such finite closure is asserted for arbitrary settings.

These are finite proof constructions, not a rule reflecting arbitrary numeric
correctness into the object calculus at unrestricted open inputs. They do not
derive unrestricted `ArrowCodomainInversion body TV`, supply all application
guards, or install a refitted checker in the actual all-type slot. The previous
finite-refit impossibility result #1475 remains intact. Definitions and intended
scope are in [INTERNAL-TYPES-SOURCE-MAP.md](internal-types/INTERNAL-TYPES-SOURCE-MAP.md).
The independent [internal-type source review](ordinal-frontier/INTERNAL-TYPE-SOURCE-REVIEW.md)
confirms these exact boundaries and finds no material statement mismatch.

## Native validation

Root owns the serialized native gate and acceptance records. The successful
focused receipts are:

| Gate | Receipt | Confirmed result |
| --- | --- | --- |
| 01 | `1795411144544945494-11` | Actual Ω-tower proof and frozen lambda definitions/targets. |
| 03 | `1795411295477093868-11` | Both structural-lambda proof modules and frozen internal-types targets. |
| 05 | `1795411504802658682-11` | The complete realization conjunction used for numbered adoption. |
| 09 | `1795412014343677355-11` | All five internal finite-membership endpoints and both grammar-codomain endpoints. |

All 23 new exact aliases use only `propext`, `Classical.choice`, and
`Quot.sound`, or a subset. The initial lambda syntax proof and rejected internal
proof drafts are retained with their diagnostic receipts. No failed draft is
an acceptance source. Existing accepted Lean sources, manuscripts, source-map
snapshots, dependency/toolchain pins, checker and resource caps are unchanged.

The final [acceptance inventory](root/ACCEPTANCE.json) records all six packets,
the 23 new exact aliases and the reused iteration endpoint. The
[focused audit](root/AUDIT.json) confirms all preproof freezes, current accepted
source hashes, exact native receipt/log origins, standard axiom sets, unchanged
prior Lean/manuscript bytes, and the two intended register changes. The
[portable evidence archive](root/portable-native-evidence.zip) includes the
receipts, focused native logs and diagnostic failures. Five failed source
drafts are preserved separately before repair.

The [stop record](root/STOPPED.json) confirms an empty serialized queue and no
remaining Lean/Lake process. The local run policy is paused after completion.
A subsequent user continuation can release the next scoped proof round.

## Remaining five numbered statements

| Pending Paper 16 statement | Remaining obligation |
| --- | --- |
| `lem:arithmetic-accessibility` | Supply the internal arithmetic accessibility proof for the actual encoded interpretation. Finite membership/grammar rules alone do not construct the uniform accessibility sentence. |
| `thm:upper` | Instantiate the internal accessibility supplier and the ID₁ norm theorem for the intended BH bound. The existing rank-to-stage-norm and conditional upper routes remain available. |
| `lem:tower-cofinality` | Construct the intended collapse, hereditary coefficient norm and criticality data, then establish their calibration and endpoint hypotheses. The actual Ω-index theorem supplies only the index-order portion. |
| `thm:height` | Instantiate the intended ordinal calibration, tower/cofinality and BH identification, together with the ordinary-term upper bound. The actual native witness sequence and its primitive-recursive codes remain checked. |
| `thm:main` | Supply the remaining upper-bound and ordinal ingredients in the combined uniform coded-effective main theorem. Its five named hypotheses remain explicit. |

Those five hypotheses are exactly `NormTheorem BH`, `UniformAccessibility`,
`Calibration D`, `TowerHypotheses D`, and `BHIdentification D BH`. The actual
Ω-index result, structural lambda theorem and earlier tower-code theorem do not
assume them. They also do not silently instantiate them. The norm/accessibility
interfaces use the empty logical assumption list; their numerical source/context
parameter is not a logical assumption context.
