# Deriving open-term facts about the checker programs inside ID₁: is there a general method? (Opus B, round 6)

**Problem.** `UniformAccessibility` still rests on nine arithmetic obligations, M1–M9 (`ACCESSIBILITY-PLAN.md`). Each says that some relation between the graphs of concrete Gorbow programs (the four checkers and the application, substitution, union, singleton and member programs) holds for **arbitrary open terms**, and each must be an actual `Derivation` in the ID₁ calculus. The question is whether one tool can produce them, rather than nine separate efforts the size of M1.

**What the repository already has, for every program and arbitrary open terms:**
- `InternalRecursionClosureTargets.ActualOriginalPrograms`: totality and functionality of every program's graph.
- `programCases`: elimination of the existential output.
- `programCompositionCases` and the composition intro/elim targets in `InternalGraphCompositionTargets`.
- Recursion zero and successor introduction/elimination (`InternalRecursionGraphTargets`).
- `valueUnique`.
- `natInduction`, list induction (`ActualOriginalListInductionAtCode`) and slice induction.
- Internal laws for the base operations: addition, multiplication, less-than, equality test, Nat.pair (`pairingSpec`), the list codec, raw list recursion.
- `numeral_evaluation_exact` for closed numerals.

So the per-constructor rules exist. What is missing is a way to combine them that does not require writing a new proof for each obligation.

## Candidate 1: Σ₁-completeness or reflection — rejected
- **Σ₁-completeness (`numeral_evaluation_exact`) does not reach M1–M9.** It gives one derivation per closed numeral instance. M1–M9 are Π₂ statements in open terms, such as "edge(f,g) ∧ accepts(g,u,v) → ∃w accepts(f,u,w) ∧ edge(w,v)". ID₁ has no ω-rule, so per-numeral derivations cannot be assembled into one derivation uniform in the free variables. That is exactly the gap the matching rounds have been working on.
- **A reflection principle is not viable.** "If an external Lean proof of a graph property has shape X, then its internal version is derivable" requires a verified translation from a fragment of Lean proofs about `evaluate` into `Derivation`s. That is a formalization of PA-provability for a proof language, and it is larger than all of M1–M9 together. A narrower soundness principle would also not be admissible here: the calculus is fixed, and adding a reflection rule changes the theory that `thm:upper`'s norm bound is about.

## Candidate 2: a symbolic-evaluation library — recommended, with limits
Derived rules that run a program's graph on open inputs of **known constructor shape**, by structural recursion on the program:
- **(a) Composition:** chain `programCompositionCases` and composition introduction through the AST. This exists piecewise; the missing part is a uniform driver.
- **(b) Recursion at a constructor-shaped counter:** unfold the successor rules finitely many times when the counter is `succ^k t`. Exists piecewise.
- **(c) Missing: branch selection on open tests.** For `InternalAcceptance.branch` and the equality, zero and less-than tests, a test whose value is fixed by the *shape* of its open input must select its branch internally. For example, the tag test on `2·t+1`, or a pairing component of `pair(h,t)`. Today each use proves this by hand; it needs per-test "decided-by-shape" lemmas.
- **(d) Missing: a code-shape vocabulary.** Internal decoding equations for the checkers' input encodings. For Paper 16 these are the `encodeFields` cells over the `(a+b)²+a` pairing, the address/type codes, and the raw-term codes. These are not the Nat.pair lists the internal list induction uses (`consCode`); this mismatch is real and must be bridged once.

With (c) and (d), an obligation whose statement fixes the input shape and needs only a bounded unfolding becomes "run the evaluator, then compare outputs". That covers the finite-shape parts:
- M3, typed probe totality on arrow codes;
- M5, inversion of application edges by head shape;
- M8, edges out of constructor codes;
- M9, decoding of admitted addresses;
- the base cases and `NilNoStep` / `SingletonCarrier` of M7.

The library does **not** remove the induction from M1 and M2 (paths of arbitrary length), M4 (fresh variables at all types), M6 (substitution under arbitrary terms), or M7b/M7c (arbitrary multisets and certificates). Those still need invariants written by hand, with the evaluator only discharging their steps.

**Size estimate.**
- Library, items (a)–(d): about 2–3 rounds of the J-union size. The (d) encoding bridge is the largest part.
- With the library: the five finite-shape obligations at under a round each. The five induction-bearing ones (M1, M2, M4, M6, M7b/c) at 1–3 rounds each, against "several rounds each" without it.
- So the library roughly halves the remaining arithmetic. It does not collapse it.

**First test case.** `NilNoStep` from this round's `ConditionalJSingleton`: the direct-replacement checker rejects every certificate out of the empty multiset code. It is open in the target and certificate, needs (a)–(d) on the actual `data.direct` program, and needs no induction, so it isolates the evaluator. Second, `SingletonCarrier`, then M5.

**Conclusion.** No method beats the direct route for the induction-bearing obligations. For the finite-shape half, a symbolic-evaluation library (branch-by-shape plus encoding bridge) does beat it and should be built first. Neither Σ₁-completeness nor reflection is a viable shortcut.
