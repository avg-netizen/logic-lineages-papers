# What separates `ClosedBlockDecision` from Paper 17 `thm:ground` (and `thm:main`) — Opus A, 2026-11-22

Register status (`CURRENT-COMPARISON-TARGETS.json`): P17 has 33 numbered statements; 30 are checked. Pending:
`thm:main`, `thm:arithmetic`, `thm:ground`.

**Headline: `thm:ground` is assembly only — no new mathematics — once `ClosedBlockDecision` is
unconditional.** Every mathematical step of its printed proof is an accepted record or a gated statement. What
is missing is (a) a frozen statement of `thm:ground` itself, (b) one elementary lemma, and (c) a
scalar-to-circuit compiler with its correctness, which is induction over accepted gate semantics. I have not
started it.

## thm:ground, step by step

| Proof step (consequences.tex) | Covering record / declaration | Status |
|---|---|---|
| The statement: universal weak, WW strict, and universal equality of canonical assignments, for original T terms with ground free variables, of any types, decidable for `f_*` and each `f_b` | — none. Paper 18's analogue for the standard control has this shape: `StandardControlCurrent.PolicySourceEqualityTargets.{TypedEquality,RawEquality,Programs}` | **missing (M2)**, definitional |
| "The generated-source theorem gives `can A_i = a_i` (closed), `can A_0 = E_A(x)` (circuit, fixed nonzero limit heads `< ε₀`, shared names)" | `thm:generated-source`, checked, #261: `SelectedGeneratedSourceTargets.FullSelectedGeneratedSource`. It contains `TypedImage` (positive coordinates closed, with `encodedClosedPositive` codes; scalar = `Scalar` tree, `vectorValueWith = denoteWith`), `FixedHeads`, `CircuitComputable`, `Programs` (raw `compile` computable), and `RawInterface` | **covered** |
| "Every positive integer is an admissible ground value … inputs range independently over ℕ_{>0}" | Grade-0 `ClosedGrade` expressions are `one`/`add` (`SelectedSourceDomainDefinitions`). There is no P17 lemma stating the bijection with positive naturals (Paper 18 has `GroundDomain` for the standard control) | **missing (M1)**, elementary |
| "First compute the finite positive-coordinate comparisons, zero padding" | Closed coordinates are NF notations (`encodedClosedPositive` Primrec, #261). Raw ordinal comparison: `OrdinalComparison.rawComparisonCode` + `rawComparisonOrdinalCorrect` + Primrec (already reused in #1393) | **missing (M3)** as a statement; pure assembly |
| "universal weak comparison is exactly the absence of ∃x∈ℕ_{>0}^r. E_A(x)>E_B(x)" (strict: `≥`, equality: `≠`) | Logic over M1 + `TypedImage` (`vectorValueWith` agrees with the assignment value) | part of **M5** |
| "Flatten the scalar circuits using unique graph coordinates and true norm guards; one existential block" | Needs `Scalar ι` → `(known, List Gate, NormalForm.Formula)`:<br>• `.one`/`.add`/`.var` become affine gates, with input = base+1 to get positivity;<br>• `.shift c a` becomes a collapse `Wire` with head `scalarHeadNote c`, whose `repr = fixedHead c` (accepted, `WWEncodedScalarDefinitions`/`SelectedGeneratedSourceHeadsProof`);<br>• the matrix is one plain row (`E_A − E_B − 1 ≥ 0`, `E_A − E_B ≥ 0`, or a disjunction for `≠`).<br>Semantics comes from `ExactPrintedCircuitRun`, `ArbitraryFixedHeadCollapse.ActualGraph` and the affine read. On codes, recursion over the accepted `scalarCode` (it already carries `rawNoteEncode` of the head) | **missing (M4)**, assembly |
| "Theorem thm:arithmetic decides this closed sentence" | `ClosedBlockDecision` (Decides: `HasSuccessfulObservation` polarity `true`) | **covered conditionally.** It needs only the guard program (Opus B); then it is unconditional |
| "This proves all three claims" (one computable decider per relation, uniform in the policy) | #261 `Programs` (`compile` computable for every effective policy) + M3 + M4 + `ClosedBlockDecision` | **missing (M5)**, assembly |

## Missing statements, smallest first

1. **M1 `SelectedGroundDomain`**: for ground Γ, every `ρ : OrdinalComponent Γ → ℕ` with `∀ c, 0 < ρ c` is
   `valuation ctrl s` for some `s : AdmissibleSubstitution ctrl Γ`, and conversely. This is the P17 copy of Paper 18's
   `GroundDomain`. *Assembly:* grade-0 closed expressions are finite sums of ones. Small.
2. **M2 Targets for `thm:ground`**:
   - `vectorAt` with zero padding;
   - `Weak a b := ∀ s j, vectorAt a s j ≤ vectorAt b s j`;
   - `WWStrict := (∀ s, coord 0 <) ∧ ∀ j>0, ∀ s, ≤`;
   - `Equal`;
   - `SelectedGroundDecision ctrl := ∀ policy effective, ∃ decide computable, ∀ Γ ground, ∀ τ υ (a : OriginalTerm Γ τ) (b : OriginalTerm Γ υ), decide (code a b) = true ↔ R(assignment a, assignment b)`, for each of the three relations, at `factorialControl` and every `nearControl b`.

   *Definitional only*, but must be checked against paper.tex l.76–80.
3. **M3 positive-coordinate decider**: raw comparison of the closed coordinate codes equals the ordinal comparison of
   `c.evaluate.repr`, padded. *Assembly* of `rawComparisonCode` and #261 codes.
4. **M4 scalar circuit compiler**: `circuitOf` on `scalarCode` pairs with `Topological`, `PlainPreparedFormula`, and
   `HasSuccessfulObservation f gs p true ↔ ∃ x : ℕ^r positive, scalarValueWith f x E_A R scalarValueWith f x E_B`, plus
   `Primrec`/`Computable` on codes. *Assembly* (induction on `Scalar` over accepted gate semantics; no new
   arithmetic). The largest item, but routine: comparable to `StageEmitterRow`.
5. **M5 the decider**: compose #261 `compile`, M3, M4 and `ClosedBlockDecision`. *Assembly.*

## thm:main

- **(i)** is `thm:ground` for `f_*` and every `f_b`, "uniformly in a supplied computable admissible policy". That is
  M2's policy quantifier; nothing else is needed.
- **(ii) and (iii)** are **already checked**: `thm:functional-hardness`, #339,
  `SelectedFunctionalHardnessTargets.SelectedFunctionalHardness`. It covers every selected control and every policy:
  - finite-query reductions with no decider at level 2, weak and strict;
  - single-query reductions with no decider at level 3.
  - The standard-control corollary is #404.
- **The control description is checked:**
  - "explicit … primitive recursive" and growth: `lem:control`, #010 `Targets.FullControl`;
  - `f_b = G` on `[0,b]` and `0 ≤ f_b − G < 2L(n)`: `Targets` line 12 and the definition.
  - The word "permitted" is the paper's framework notion. I did not trace a separate Lean predicate for it.

So `thm:main` = M1–M5 (= `thm:ground`) + a conjunction with #339 and #010. That is assembly, a few lines once
`thm:ground` exists.

**Order of work if root approves:** M1, M3, M2 (freeze), M4, M5, then the `thm:main` conjunction. All of it depends
only on accepted material plus an unconditional `ClosedBlockDecision`.
