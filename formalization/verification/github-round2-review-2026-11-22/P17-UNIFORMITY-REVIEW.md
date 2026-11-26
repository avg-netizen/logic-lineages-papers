# Paper 17: independent source review of the uniform comparison repair

## Review identity and outcome

- Reviewed repository head: `1cd1734feb2b64c5a9936b2b5e8649f9b2f3889c`.
- Earlier published checkpoint: `a14a936772e01363795c919c106607fdad368f8c`.
- Scope: the new Paper 17 uniform-policy compiler, joint near-control closed-block procedure, their assembly, and the strengthened `UniformMainComparison` comparator. The relevant supporting records are #1437, #1439, #1441, #1444, and #1445.
- Method: compare the actual propositions and their semantic implementations with the printed source, using previously accepted interfaces for canonical assignment, circuit semantics, control laws, and hardness. Native proof validity relies on the recorded gates. This review does not duplicate the native compilation gate or a full proof-body/artifact replay.
- Result: **no material source-correspondence mismatch found in the new uniformity repair**. The strengthened comparator closes the supplied-policy-program and joint near-control-parameter gaps identified in the earlier correspondence review.

All paths and line references below are repository-relative at the reviewed head. Within a paragraph or table row, a shortened Lean filename continues the directory `formalization/LogicLineages/PermittedControl/`; a shortened `paper.tex` or `sections/` reference continues `17-permitted-control-canonical-comparison/`. No accepted source, register entry, pin, or historical validation statement was changed by this review.

## Five printed clauses checked

The five obligations are the opening control/uniformity clause, the three numbered comparison clauses, and the final near-control clause of `17-permitted-control-canonical-comparison/paper.tex:83–100`.

| Printed obligation | Formal counterpart and source location | Assessment |
|---|---|---|
| An explicit permitted primitive-recursive control, with the assertions uniform in a supplied computable admissible literal policy (`paper.tex:84–86`). | `formalization/LogicLineages/PermittedControl/UniformGroundComparisonTargets.lean:68–72` includes `Targets.FullControl`; `ControlTargets.lean:10–22` gives the laws for the explicit factorial and near controls. `UniformGroundComparisonTargets.lean:28–36` quantifies one partial-recursive procedure before the supplied program and policy. | The old policy-uniformity gap is closed. The inherited meaning of permittedness remains the explicit control-law interface, as described below. |
| Clause (i): weak comparison, strict comparison, and equality are decidable for original T terms with ground free variables, without restrictions on bound variables, result types, internal types, or recursors (`paper.tex:88–91`). | `formalization/LogicLineages/PermittedControl/UniformGroundComparisonTargets.lean:28–36` and `40–49` quantify arbitrary result types and arbitrary well-typed `OriginalTerm` values, restricting only the free context to ground types. `GroundComparisonTargets.lean:10–40` specifies the three canonical vector relations. | Matches the source domain and relation meanings. The target has no additional type-level or recursor bound. |
| Clause (ii): weak and strict comparison are undecidable for ground output, free-variable levels at most one, and internal levels at most two, via a finite-query reduction (`paper.tex:92–94`). | `formalization/LogicLineages/PermittedControl/SelectedFunctionalHardnessTargets.lean:10–19` includes the two no-decider conclusions. `SelectedFiniteQueryTargets.lean:10–17` supplies a fixed primitive-recursive code function and an exact reduction to a finite conjunction of level-two universal queries. These are explicit conjuncts of `UniformMainComparison`. | Matches the bounds and finite-query meaning. The reduction is from polynomial-system unsatisfiability, with the conjunction direction stated explicitly. |
| Clause (iii): a single-query reduction is available when internal levels at most three are allowed (`paper.tex:95–96`). | `formalization/LogicLineages/PermittedControl/SelectedSingleQueryTargets.lean:8–11` and `21–28` give a fixed primitive-recursive single-query program, ground output, free-variable level at most one, internal level at most three, and exact unsatisfiability equivalence. | Matches the printed single-query claim. No level-two single-query claim or stronger completeness classification is introduced. |
| For every supplied `b`, the same assertions hold at an explicit `f_b`, with the stated preserved prefix and distance bound (`paper.tex:98–100`). | `formalization/LogicLineages/PermittedControl/UniformGroundComparisonTargets.lean:40–49` takes `b` as a runtime input before the query. `UniformNearClosedBlockTargets.lean:21–41` gives a single jointly computable closed-block family. `Targets.lean:9–15` supplies prefix agreement, domination, and the `2 * initialLcm` distance bound; `ControlTargets.lean:21–22` supplies the near-control laws. Hardness programs are independent of both policy and control. | The old joint-in-`b` gap is closed. The same fixed reduction codes serve every near control. |

## Supplied policy programs and quantifier order

The printed policy is a computable ordered full binary addition-tree selector depending only on macro site and arity, preserving operands and existing subtrees: `17-permitted-control-canonical-comparison/sections/source.tex:132–148`. The new interface uses exactly the existing selector representation. In `formalization/LogicLineages/PermittedControl/PolicySuppliedCodeMacroInterpreterTargets.lean:13–15`, `RealizesPolicy e p` means that the ordinary program `e` evaluates to the encoded selector of `p` at every site and arity.

The new positive comparator has the relevant quantifier order:

```text
for each relation,
  there exists one partial-recursive procedure,
    for every supplied program and realized policy,
      the procedure halts and gives the required typed-source answers.
```

At the near controls, the quantifier over `b` is also inside the existential over the procedure, and `b` is part of its runtime argument. These are the definitions in `formalization/LogicLineages/PermittedControl/UniformGroundComparisonTargets.lean:28–49`. They are stronger than choosing a separate computable decider after each policy or after each `b`.

The interface does not shrink the admitted effective policy class. `formalization/LogicLineages/PermittedControl/PolicySuppliedCodeRealizationTargets.lean:25–27` states

```lean
∀ p, PolicyShape.Effective p ↔ ∃ e, RealizesPolicy e p
```

The source supplies a policy program. It does not require computably choosing a program from an abstract semantic policy. The realization bridge is therefore the appropriate coverage statement. Invalid alleged policy programs may diverge; recognizing the set of valid total policy programs is not required.

There is one procedure per relation rather than an additional runtime relation tag. This is immaterial to the theorem: `GroundComparison.Relation` has exactly the weak, strict, and equality constructors (`formalization/LogicLineages/PermittedControl/GroundComparisonTargets.lean:10–14`), and finite case selection combines their procedures.

## Termination, rejection, and the actual compiler

`formalization/LogicLineages/PermittedControl/UniformPolicyCompilerTargets.lean:14–22` requires one partial-recursive compiler, with its existential outside all programs and policies. On any realizing program it satisfies exact equality for every raw context length and raw term code:

```lean
compilePolicy (e,d,c) = Part.some (PolicySourceInterface.compile p d c)
```

This equality proves termination on the entire raw input domain when the policy program is valid. It also distinguishes source rejection, represented by `Part.some none`, from divergence of the outer `Part`.

The semantic implementation preserves that distinction. `formalization/LogicLineages/PermittedControl/UniformPolicyCompilerFixProof.lean:15–16` performs decoded ordinary program evaluation. Its `pbind`, at lines 58–59, propagates outer divergence while keeping an inner `none` as a terminating rejection. `UniformPolicyCompilerProof.lean:13–19` fixes one partial-recursive assignment evaluator, independently of any supplied policy. Its `Classical.choose` selects a certified partial-recursive fixed point, not an oracle or a fresh evaluator chosen after each policy. `UniformPolicyCompilerProof.lean:60–84` composes this evaluator with the policy-free vector compiler and supplies exact calibration and the final existential compiler theorem.

The comparison assembly compiles both terms through that supplied-code evaluator and then uses the existing comparison body. Compiler rejection becomes `false` at the final Boolean layer (`formalization/LogicLineages/PermittedControl/UniformGroundAssemblyProof.lean:40–42`). This agrees with the target: malformed raw inputs must halt for a valid policy program, but only well-typed ground-context source codes carry a required comparison meaning. For typed terms, the assembly obtains successful compiler images before invoking the semantic reduction (`UniformGroundAssemblyProof.lean:165–186`). Rejection is not used to justify a typed-source comparison.

## Joint computation at the near controls

`formalization/LogicLineages/PermittedControl/UniformNearClosedBlockTargets.lean:21–23` defines one concrete function:

```text
nearDecide (b,x) = the raw stage query at nearControl b,
                  threshold b+1, with one fixed rendering/high program.
```

The family is not merely asserted correct separately at each `b`. `ParametricSolveEffectivity` at lines 27–30 requires joint computability when the control and bound functions are computable in their parameter. `NearDecideComputable` at line 33 applies to the combined `(b,x)` function. `UniformNearClosedBlockDecision` at lines 39–41 places the chosen procedure outside `b`.

The implementation connects these statements to `Computable₂ nearControl` and the jointly computable stage bound (`formalization/LogicLineages/PermittedControl/UniformNearClosedBlockProof.lean:30–46`). The assembly's family theorem chooses its procedure before the parameter and policy (`UniformGroundAssemblyProof.lean:147–154`); its near-control instance passes this same near decider at `P := Nat` (`UniformGroundAssemblyProof.lean:217–219`). No separate nonuniform choice at each `b` remains.

## Canonical comparison and circuit domains

The strengthened target keeps the accepted canonical semantics. `formalization/LogicLineages/PermittedControl/GroundComparisonTargets.lean:18–40` defines zero-padded vectors, coordinatewise universal weak/equality comparison, strictness in coordinate zero with weakness in positive coordinates, and comparison of the literal canonical assignments. This matches `17-permitted-control-canonical-comparison/paper.tex:76–81` and `sections/consequences.tex:3–7` and `31–39`.

The decision body checks closed positive coordinates and negates the scalar-counterexample query (`formalization/LogicLineages/PermittedControl/UniformGroundAssemblyProof.lean:34–38`). The query interface equates successful circuit observations with counterexamples over shared positive inputs (`GroundComparisonAssemblyTargets.lean:16–25`). `ClosedBlockDecisionTargets.lean:21–29` supplies both the existential truth value and its exact negation, and interprets universal queries through opposite output polarity.

These interfaces retain the printed circuit-domain convention. Graph equations remain conjoined outside the possibly negated output test; universal truth means absence of an existential counterexample on the same original circuit domain. The source states this in `17-permitted-control-canonical-comparison/sections/arithmetic.tex:34–43` and `271–273`, and uses it for canonical comparison in `sections/consequences.tex:31–44`. The uniformity repair introduces no alternative semantics for unsuccessful circuit runs.

## Hardness directions and uniformity

The printed source problem is solvability of finite linear systems over polynomial unknowns, allowing zero polynomials; the paper imports undecidability without claiming a stronger completeness classification (`17-permitted-control-canonical-comparison/sections/hardness.tex:9–19`). Its comparison reductions use unsatisfiability (`sections/hardness.tex:171–178`, `188–211`, and `213–241`).

The finite-query target states

```text
not encodedPolynomialSolvable e
  iff every emitted level-two query is universally true.
```

The query-code list is literally `FiniteQueryCode.reduceCode strict e`, with a separate primitive-recursiveness assertion (`formalization/LogicLineages/PermittedControl/SelectedFiniteQueryTargets.lean:10–17`). Thus the existential semantic query list cannot replace the executable reduction by a policy-dependent search.

The level-three target states the analogous equivalence with one ground-output source pair, whose packed code is literally `SeededQueryCode.reduceCode strict e` (`formalization/LogicLineages/PermittedControl/SelectedSingleQueryTargets.lean:21–28`). Its primitive-recursiveness is explicit at lines 8–11. Both programs are independent of policy and control, while their correctness is quantified over every selected control and every policy. This gives the required uniform reductions for both relations and all near parameters. The no-decider conjuncts remain explicit in `SelectedFunctionalHardnessTargets.lean:10–19`.

## Completion, inherited boundaries, and promotion recommendation

`formalization/LogicLineages/PermittedControl/UniformGroundComparisonProof.lean:12–19` supplies `uniformGroundComparison` and `uniformMainComparison` without hypotheses, using the uniform compiler and joint near-control closed-block theorem. The supporting chain is #1437/#1439/#1441/#1444/#1445. Their record locations are under `formalization/verification/new-paper-set-2026-11-18/accepted/` with the respective names `1437-p17-uniform-main-reduction.json`, `1439-p17-uniform-ground-assembly.json`, `1441-p17-joint-near-closed-blocks.json`, `1444-p17-uniform-policy-compiler.json`, and `1445-p17-uniform-main-comparison.json`.

The new source maps accurately describe the semantic scope:

- `formalization/verification/local-fable-pair-2026-11-22-round2/root/UNIFORM-MAIN-SOURCE-MAP.md:11–27` and `31–52`;
- `formalization/verification/local-fable-pair-2026-11-22-round2/opusA/UNIFORM-POLICY-COMPILER-SOURCE-MAP.md:12–16` and `62–76`;
- `formalization/verification/local-fable-pair-2026-11-22-round2/opusB/UNIFORM-NEAR-CLOSED-BLOCK-SOURCE-MAP.md:10–35`.

Two inherited boundaries remain explicit. First, canonical-assignment, admissibility, source encoding, and flattened-circuit semantics are the accepted interfaces reused by the earlier comparisons; this targeted review did not reopen their full proof development. Second, permittedness is represented by the explicit numerical control laws in `ControlTargets.lean:10–22`, not by a separate formal port of Wilken–Weiermann §2.1. The root source map records that boundary at lines 50–52. Neither boundary is a new uniformity defect.

**Recommendation:** #1445 and its strengthened alias `LogicLineages.PermittedControl.UniformGroundComparison.uniformMainComparison` are ready for a numbered `thm:main` promotion decision under the established semantic interfaces, subject to the owner's independent native/evidence and register checks. The specific correspondence objection to #1429 is resolved by #1445; it should not be resolved by relabeling #1429's weaker proposition. No numbered promotion or register change is made here.

The creation-time statement in `formalization/verification/local-fable-pair-2026-11-22-round2/root/1445-SCOPE.txt:1` that the comparator had not yet been read against the printed theorem is historical. This document supplies the subsequent independent comparison. A current handoff may link to this result without rewriting that historical scope statement.
