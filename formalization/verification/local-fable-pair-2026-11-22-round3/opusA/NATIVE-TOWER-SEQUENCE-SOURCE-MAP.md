# NATIVE-TOWER-SEQUENCE: source map (Opus A, round 3; successor of `NATIVE-TOWER-SOURCE-MAP.md`)

This serves `ordinals.tex` 564–590: the sequence (D) and the native terms `t_n` of (R). It covers the paper's own
composites only, not the identification `Δ_n = ψ_B(a_n)`.

## Gated

| Module (`LogicLineages/NativeModule/PersistentMarking/`) | sha256 | Receipt |
|---|---|---|
| `NativeTowerSequenceTargets` (frozen; compiled alone) | `830ba1663446ed317e15e9bd1fa9b584d1122552b0972e3dfd791ca0c65eb754` | `1795402872232949190-3279494` |
| `NativeTowerSequenceProof`: `exact_NativeTowerSequenceRealization : NativeTowerSequenceRealization` | `25998ef946d6e77fd74cec10f2788ab834f8b7c1637282a9a3d6ba87ae8553cf` | `1795402918597835057-3279644` (688 modules, all rc 0) |

- Axioms: `[propext, Classical.choice, Quot.sound]`.
- RSS: the compiled module peaked at 941,296 KiB, and the closure peak is 945,812 KiB (`NativeTowerProof`). The cap is
  1,572,864 KiB.

**Statement.** Fix a signature `S`. Take any semantic `Z, s, add, mul, w, one, pow, fix` satisfying the paper's
arithmetic and ω equations (`OrdinalArithmeticEquations`, `OmegaArithmeticEquations`; these have solutions by the
generic orbit records). Then for every `n`:
- the printed native term `t_n` is a closed native term of type σ;
- it realizes `Δ_n'`, which at ι is `r_σ(t_n) ≥ Δ_n'`.

## Printed text against the definitions

| Printed | Lean | Verdict |
|---|---|---|
| "N_B = B_1 B_0 Next" | `veblenTerm = app (app B_1 B_0) ordinalNext`, where `B_l = towerTerm ordinalFix l` (#1459's term) and `ordinalNext = fix pow`. Semantically, `veblenValue = B_1(B_0)(fix pow)`. | literal |
| "ε_B = Γ_0 = N_B(ω)" | `baseTerm = app veblenTerm omegaCarrier`, where `omegaCarrier` is the printed `w = Cap(s,Z)`. Semantically, `baseValue = N_B(w)`. | The composite `N_B(ω)` is literal. "`= Γ_0`" is Simmons's identity (after Lemma 6.6) and is not stated. |
| "Δ_0 = Γ_0" | `sequenceTerm 0 = baseTerm`, `sequenceValue 0 = baseValue` | literal, with `Γ_0` read as `ε_B = N_B(ω)` |
| "Δ_1 = N_B Γ_0" | `sequenceTerm 1 = app veblenTerm baseTerm` | literal |
| "Δ_{l+2} = B_l B_{l-1}⋯B_0 N_B Γ_0" | `sequenceTerm (l+2) = app (app (downTerm l B_l) veblenTerm) baseTerm`, where `downTerm l v = v B_{l-1} ⋯ B_0`. Semantically, `downValue`. | literal (`sequenceTerm_two`, `sequenceTerm_three`) |
| "Replace the operations in (D) by their native realizers and call the resulting closed terms t_n" | `∃ t : term ι, t.val = sequenceTerm n` | checked: every `t_n` is closed native |
| "Each has actual outer type σ = o→o" | `t : (nativeTerms S).term .base` = `ClosedNativeTerm S σ` | checked |
| "r_σ(t_n) ≥ ψ_B(a_n)" (R) | `Realizes .base t (sequenceValue … n)`, that is, `Δ_n' ≤ r_σ(t_n)` | the self-contained half. `Δ_n' = ψ_B(a_n)` is external (see below). |

**Where `a_n` enters.** Only in the interpretation, never in the term: (D) and the `t_n` mention only `B_l`, Next and
`ω`. So (D) is written down completely without ψ_B, norms, helpfulness or BH.

The proof is application all the way down: arrow realization by definition, plus induction on `l` for `downTerm`.
Its inputs:
- `B_l` realizers: #1459.
- `Next` and `ω` realizers: the 9th and 5th conjuncts of `exact_LiteralNativeArithmeticRealizes` (#1456 closure).

## `thm:height`: every printed step

Printed: "The realizers (R) and Lemma tower-cofinality give the lower bound for the restriction to closed native terms.
Its ranks are bounded by the ranks in the full ordering. Theorem upper bounds each individual full rank below BH.
Taking the supremum of ranks plus one gives equality."

| Step | Status |
|---|---|
| Realization closure, finite chains, abstraction rule (`lem:realization`, native) | compiled: #1450, #1452, plus the round-2 twins of `exact_NativeRealizationClosure` / `exact_NativeLambdaRealization` |
| `thm:iteration` (native `It_A`) | compiled: twin `exact_NativeIteratorRealizesFullPrefix` (round 2) |
| `Z`, `s`, add, mul, one, `w ⊨ ω`, pow, fix, Next realizers | compiled: #1456 closure (`exact_NativeOrdinalArithmeticRealization`, `exact_LiteralNativeArithmeticRealizes`) |
| (B), (B_T): every `B_l` realized | compiled: #1458 (generic `F`), #1459 (printed fix) |
| (D) and the `t_n`: closed native with `r_σ(t_n) ≥ Δ_n'` | compiled: this module (receipt above) |
| (R), second half: `Δ_n' = ψ_B(a_n)` | **external E1** |
| `lem:tower-cofinality`: `sup_n ψ_B(a_n) = ψ_B(Λ) = BH` | **external E2 and E3** (the small ordinal argument given (P) is internal, not compiled) |
| "lower bound for the restriction": height of ⊐ on closed native σ-terms ≥ `sup_n (r_σ(t_n)+1)` | internal and elementary; **not compiled**. It needs a Lean "descending height" (sup of rank+1) and is immediate from the definition. |
| "ranks bounded by the ranks in the full ordering": restricted rank ≤ full rank | internal and elementary (Acc-rank is monotone under restriction to a subset closed under the relation's targets, or under a subrelation); **not compiled** |
| `thm:upper`, well-foundedness | compiled: #489 |
| `thm:upper`, rank domination `rk_⊐(s) ≤ rk_{R_S}(tr s)` | compiled on twins: round-2 receipt `1795399872966250102-3264833` (`exact_OriginalInitialQuoteRankDominance`). Whether `quote start` matches the printed `tr(s)` is an owner question. |
| `thm:upper`, "R_S rank = tagged I-norm" | compiled: #1454, #1455, #1460 (round 3, Opus B) |
| `thm:upper`, ID₁ proof of `I(tr s)` (`lem:arithmetic-accessibility`) | internal, large; mostly **not compiled** (gap map §4) |
| `thm:upper`, "the published norm theorem": `rk_{R_S}(tr s) < BH` | **external E4** |
| "supremum of ranks plus one gives equality" | internal and elementary, given the lines above; not compiled |

## The external residue, as statements a Lean file would have to state

All four need a Lean `Ω` (first uncountable ordinal) and ordinals beyond `CountableOrdinal`. The repository has neither
an Ω-based notation nor any collapsing function.

- **E1 — Simmons calibration of the towers.** For every `n`, `Δ_n' = ψ_B(a_n)`, where:
  - `a_0 = 0` and `a_{n+1} = Ω^{a_n}`;
  - `ψ_B` is Simmons's Veblen-hull collapse (2004 §5).

  The cited route also includes three further facts:
  - the semantic `fix` (value `f^ω(z+1)`) agrees with Simmons's `Fix` on the functions that occur (helpfulness,
    2008 Thm 5.10);
  - `ε_B = N_B(ω) = Γ_0` (the identity after 2008 Lemma 6.6);
  - the tameness / coefficient-norm hypothesis of 2004 Thm 6.1 / Cor 6.2.

  To state it, Lean needs: Ω; ordinal exponentiation above Ω (Mathlib has `Ordinal` exponentiation); `ψ_B` as a
  collapse via hulls closed under Veblen-type functions; the base-Ω coefficient norm; and Simmons's helpfulness
  classes at every finite type.
- **E2 — characterization (P).** `ψ_B(ξ)` is the least `N_B`-critical θ such that `η < ξ ∧ |η| < θ → ψ_B(η) < θ`
  (Simmons 2004 §5). Lean needs: `ψ_B`, the coefficient norm `|·|`, and `N_B`-criticality (orbit values
  `N_B^α(Γ_0)`). Given E2 and the norm bound `|a_n| ≤ 1`, the printed cofinality argument is a short internal proof.
- **E3 — endpoint identification.** `ψ_B(ε_{Ω+1}) = BH`, where BH is the Bachmann–Howard ordinal of the
  inductive-norm calibration (Pohlers §§9.4–9.5). Lean needs: `ε_{Ω+1}`, `ψ_B` from E1, and a definition of BH, for
  example as the sup of norms of ID₁-provable positive inductive memberships, or by Pohlers's own collapse.
- **E4 — Pohlers's norm theorem.** Every ID₁-provable positive membership `I(t)` has inductive norm `< BH` (Pohlers
  Defs 6.3.1, 6.3.5, 9.1.2; Lemma 6.5.2; Thms 9.5.5–9.5.6). Lean needs: the ID₁ language and provability, the stage
  norm of the inductive operator (the repo has the tagged stage norm, #1454–#1460), and BH. This is an ordinal analysis
  of ID₁.

Besides E1–E4, `thm:height` still needs three internal pieces, none external:
1. The ID₁ proof of `I(tr s)` (`lem:arithmetic-accessibility`, large).
2. The two elementary rank and height facts.
3. The short (P)-based cofinality argument.
