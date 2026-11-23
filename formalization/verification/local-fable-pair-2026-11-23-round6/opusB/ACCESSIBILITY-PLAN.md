# `lem:arithmetic-accessibility` as internal statements: dependency order (Opus B, round 6)

## Update 23 Nov (later): guard wrapper and design recommendation (earlier text below is unchanged)

**Status changes.**
- `NilNoStep` is now a **theorem for a guarded, equally admissible presentation** (`ConditionalJGuardProof.exact_GuardNilNoStep`, receipt `1795415061808575178-3320260`). It is *not* a theorem about the original witness `d`. The guarded checker `guardedDirect d := branch (projection 0) (constantZero 3) d` satisfies the same `Evaluates` (`exact_GuardEvaluates`, using `directAtZero`).
- J-singleton and J-members are re-closed on `data i j r (guardedDirect d)` without `NilCarrier` and without `NilNoStep` (`exact_GuardedJSingleton`, `exact_GuardedJMembers`).
- `SingletonCarrier`: the same device applies, but is **not yet done**. The singleton program would be the explicit `NumberedWindowInternalSparsePair.fieldCons(q, 0)`. The guard on the multiset-domain program would select `i(left(s−1))` when `good(s−1) = 1` and `right(s−1) = 0`. Every test is visible code with an internal law: #1457 `exact_OpenSuccess`/`exact_OpenFailure`, and `OpenFieldConsGraph`/`OpenFieldConsInjective`. The guard only *calls* the opaque scalar checker `i` as a black box. Estimate under one round.

**Design recommendation for whoever continues the internal line.**
- **Replace all four presentation programs by explicit program definitions,** and make their primitive-recursiveness a theorem about that visible code:
  - the scalar domain `i` (M9, carrier facts);
  - the multiset domain `j` (M7a, `SingletonCarrier`);
  - the positive-path checker `r` (M1, M2, M5, M8);
  - the direct-replacement checker `d` (M7a–c, `NilNoStep`).
- **Do the same for the application, typed-probe and fresh programs `p`, `h`, `a`** (M1–M4).
- **Why.** Today all of them exist only as `∃ p` witnesses, obtained by `NumberedWindowConcreteCheckersProgramChecks.exact_AllFourProgramWitnesses` from `NumberedWindowAddressCheckersProgramProof` and `NumberedWindowDirectProgramProof` (Primrec existence). Open-term facts are derivable only about code the calculus can see. Guards are a stopgap for rejection or acceptance facts that are decided by a visible prefix test.
- **Records pinning the existence-witness form, which would need parallel explicit versions:**
  - #563: the four checker programs;
  - #571: `exact_ConcreteInternalAccessibility`;
  - #635, #636, #676: `NumberedWindowConcreteCheckersProgram*`;
  - #653, #679, #682, #692: `NumberedWindowConcreteFormula*`;
  - the `NumberedWindowInternalAccessibility*` consumers #644, #652, #656, #659, #660, #675, #676, #679, #682, #696, #713.
  - These are existing statements, quantified over programs that satisfy `Evaluates`. An explicit version must re-instantiate them at the visible programs; it does not need to edit them.

## Running premise table (added 23 Nov, after #1487/#1489; earlier text below is unchanged)

| Premise | Used by | Status | Covered by |
|---|---|---|---|
| M1 `ApplicationEdgeMatching` | #585 downward closure | open | — |
| M2 `ForwardRule` | #599 pullback | open | — |
| M3 `TypedProbeTotal` | `TypedComputabilityImpliesMembership` | open (definitions only, round 3) | — |
| M4 `FreshVariablesComputable` | same | open (ground case #662) | — |
| M5 application-edge inversion | neutral lemma | open | — |
| M6 raw step under substitution | lambda fact | open | — |
| M7a `CarrierUnion` | #1487, #1489 | open | — |
| M7b `MultisetSplit` | #1487, #1489 | open | — |
| M7c `DescendantGeneration` | #1489 | open | — |
| `MemberGeneration` | #1489 (members) | open | — |
| `SingletonCarrier` | #1489 | open; guard route identified (see update above, <1 round); for the opaque witness **blocked** like `NilNoStep` (the domain checker's `unpack` iterates on the open code as fuel) | — |
| `NilCarrier` | #1489 | **theorem** for every presentation evaluating the window's checks: `ConditionalJNilCarrierProof.exact_ActualNilCarrier`, receipt `1795414761361050081-3319071`; re-closed as `exact_ActualJSingleton` / `exact_ActualJMembers` | closed instance: `numeral_evaluation_exact` + `exact_ExactCoordinates` (no AST knowledge needed) |
| `NilNoStep` | #1489 | **theorem for the guarded presentation** (`exact_GuardNilNoStep`, receipt `1795415061808575178-3320260`); for the original opaque witness: **blocked**: (1) the direct checker is an opaque existential AST (`DirectCertificateProgram`); (2) even on a transparent AST its control flow on an open certificate is not shape-determined (see LEDGER) | — |
| M8 constructor-edge exhaustion | (L) | open | — |
| M9 admitted-address decoding | final induction | open | — |

**Goal.** `ConditionalUpperUniformTargets.UniformAccessibility`. For each closed window K there must be programs that evaluate the original checks, and an outer context c, such that `Nonempty (Derivation (sourceBody d c) [] (allTermsFormula d c))`.

**Vocabulary** (accepted internal line):
- B = `sourceBody d c`.
- I and J are `membership false x` and `membership true x` (`ID1Completion.InternalAccessibilityRules`).
- The carriers are `carrier d odd c x`; the R_S and DM(R_S) edges are `edge d odd c x y`.
- C_τ is `NumberedWindowComputabilityFormulaTargets.formula p τ q`.

"Arithmetic" below means an open-term fact about the concrete checker programs, derived inside the calculus.

| # | Printed component | Internal statement | Status, dependencies, size |
|---|---|---|---|
| 1 | (A): operators I and J with tags | `Rules` (equation, carrier extraction, successor, certified successor, introduction) for the presentation | **accepted**: #571 for the Paper 16 programs, and generically `InternalAccessibilityRulesProof.actualOriginal*` for any `data` |
| 2 | "induct on I(·)" and "induct on J(·)" | `InternalSliceInductionProof.actualInternalSliceInduction` (one tag, invariant may mention the predicate negatively) and `sliceReplacement` (the closure premise is literally `carrier v ⊓ ∀w (edge v w ⟶ θ w)`) | **accepted** (ID₁ least-fixed-point rule `inductiveLeastness`; Paper 06 line, reused by #599). This is the rule every induction below uses |
| 3 | (T): C_τ by external recursion on type | `formula p τ q`: C_o is literally `membership false q`; the arrow case is `∀u∀v (accepts p q u v ⟶ C_σ u ⟶ C_τ v)` | **accepted**: #578 (standard reading), #582 (arrow intro/elim, commutes with substitution) |
| 4 | preservation under ⇝ and R_S (downward closure) | `NumberedWindowInternalDownwardTargets.ComputabilityDownward` | accepted **conditionally** (#585) on `ApplicationEdgeMatching d p c`. That premise is **arithmetic (M1)**: from edge(f,g) and accepts(g,u,v), get w with accepts(f,u,w) and edge(w,v). Open. Large (the #1419–#1440 work is aimed at it) |
| 5 | computability ⇒ I (arrow case: fresh computable x, path lifting Qx R Q'x, induction on I(Qx)) | `NumberedWindowInternalProbeTargets.TypedComputabilityImpliesMembership` | accepted **conditionally** on: `Pullback` (#599, itself conditional on `ForwardRule`, **M2**, the forward dual of M1); `TypedProbeTotal` (**M3**, the open-term typed probe, definitions only in round 3); `FreshVariablesComputable` (**M4**) |
| 6 | variables and bottoms computable (neutral case) | M4 for variables; I(⊥_τ) for bottoms | variables: ground case only (#662). Bottoms: none. Arithmetic: bottom has no edges (open certificate). Medium |
| 7 | neutral lemma (a non-lambda with computable direct reducts is computable) | `formula p τ (app q u)` from `∀y (edge(q u, y) ⟶ formula p τ y)` for non-lambda q | none. Needs **arithmetic M5**, inversion of application edges: every edge out of `q u` with q non-lambda is `q' u` with edge(q, q'), or bottom. Large |
| 8 | lambda fact | C(λx.V) from ∀U (C U ⟶ C (V[x:=U])) | none. Needs **arithmetic M6**: a raw step under the substitution program is a raw path or an equality. Uses 2, 4, 7. Large |
| 9a | J closed under multiset union | for a union program u: J m, J n, U(m,n,o) ⊢ J o | **proved this round** (`ConditionalJUnionProof.exact_ConditionalJUnion`, receipt `1795413770153441136-3315432`, axioms propext/Quot.sound), as a premise-explicit internal double induction. Premises: **arithmetic M7a** (`CarrierUnion`) and **M7b** (`MultisetSplit`, the printed "target splits into two components…") |
| 9b | I(Q) ⇒ J({Q}); accessible members ⇒ J(M) | J(singleton q) from I(q); then list induction over M | none. Uses 9a, slice induction on I, and arithmetic **M7c**: a DM step from a singleton consists of R_S descendants. Medium, once M7 exists |
| 10 | constructor induction (L) on (head class, base multiset, label ∈ ℕ∪{ω}, extras) | nested induction: finite induction on head classes, J on base, natural numbers on label, J on extras | none. Needs **arithmetic M8**: every edge out of a constructor term is one of the eight raw rules, with its certificate. Uses 2, 4, 6–9. Very large |
| 11 | final structural induction under computable substitution ⇒ `allTermsFormula` | ∀x (carrier(x) ⟶ I(2x)) | none. Needs **arithmetic M9**: every admitted address decodes as a variable, lambda, application or constructor code. Uses 5 and 10. Large |

**Rule used for every "induct on I/J".** Item 2: `actualInternalSliceInduction d c α Γ odd θ t` with the premise `replacedBody (sliceBody d c odd) θ :: Γ.map weaken ⊢ θ`, rewritten by `sliceReplacement`. Natural-number induction is `Derivation.arithmetic (.induction θ)` or `ActualInternalNaturalInduction`.

**Honest estimate.** The logical skeletons (items 2, 3 and 9a) are now accepted or proved. What separates the repository from `UniformAccessibility` is the arithmetic obligations M1–M9: open-term properties of the four concrete checker programs and of the application, substitution and union programs, derived inside ID₁. Each is comparable to the M1 effort, which has taken many rounds and is still open. The logical skeletons of items 5–11 relative to those premises are each one round, as item 9a is here.
