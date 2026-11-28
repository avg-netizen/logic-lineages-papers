# Uniform induction over the type level — plan (Fable A2, 27 November 2026)

Written before anything uniform is frozen. Paper argument only; what is gated is in `LEDGER.md`.
Notation: `A_j = tier j`, `B_m = towerValue fix m : A_{m+2}`, slot `j` of an environment `xs : Env` holds a
value of type `A_j` (root's convention in `towerEnv`, `semDown`, `spineValue`).

## 0. Decision: flat (environment) form of the logical relation

Fable A's note proposed the curried form `Good (k+1) Φ := ∀ G, Good k G → Good k (Φ G) ∧ Dom …`.
I use the equivalent *flat* form: a predicate on `F : A_{k+1}` quantifies over a whole environment of
good arguments for the slots `k, …, 1` and speaks about the fully applied function
`appDown k F xs = F (xs k) ⋯ (xs 1) : A_1`. Reasons: `B_m` and the level diagonal are *defined* through
environments (`curryEnv`, `spineValue`, `semDown`), so the flat form needs one unfolding lemma
(`appDown (m+1) B_m xs = fix (spineValue m xs)`) instead of a currying induction per predicate; closure
under application becomes a lemma (one `Function.update`), proved once.

## 1. Definitions (to be frozen as Lean, structural recursion on `k` only through the environment)

```
appDown : (k : Nat) → Value (tier (k+1)) → Env → Value (tier 1)
  | 0, v, _ => v            | k+1, v, xs => appDown k (v (xs (k+1))) xs
domClause : (k) → Value (tier (k+1)) → Env → Prop
  | 0, _, _ => True         | k+1, F, xs => ∀ x, B_0 (appDown k (xs (k+1)) xs) x ≤ appDown (k+1) F xs x
GoodAt k E F   := ∀ xs, E xs → GoodFn (appDown k F xs) ∧ domClause k F xs
GoodEnv 0 xs   := True ;  GoodEnv (k+1) xs := GoodEnv k xs ∧ GoodAt k (GoodEnv k) (xs (k+1))
GoodF k F      := GoodAt k (GoodEnv k) F                      -- F : A_{k+1}

ExpSep ε σ     := NormSeparated ε σ ∧ |ε| ≤ |ε + Ω^σ| ∧ |σ| ≤ |ε + Ω^σ|
expDown 0 ss σ := σ ;     expDown (k+1) ss σ := expDown k ss (ss (k+1) + Ω^σ)
CondDown 0 ss σ := Ω^σ < Λ ;  CondDown (k+1) ss σ := ExpSep (ss (k+1)) σ ∧ CondDown k ss (ss (k+1) + Ω^σ)
WeightAt k E σ F := GoodF k F ∧ ∀ xs ss, E xs ss → CondDown k ss σ →
                      StepUp (Ω^(expDown k ss σ)) (appDown k F xs) ∧ StepLow (same)
WEnv 0 xs ss   := True ;  WEnv (k+1) xs ss := WEnv k xs ss ∧ WeightAt k (WEnv k) (ss (k+1)) (xs (k+1))
WeightF k σ F  := WeightAt k (WEnv k) σ F
```

`ss j` is the weight of slot `j`. An object of weight `σ` at type `A_{k+1}` applied to an argument of weight
`ε` gives weight `ε + Ω^σ` at type `A_k`; at type `A_1` weight `σ` means "`(Ω^σ, H)` is a step".

Changes against Fable A's corrected `ExpCond` (both forced by weights that are no longer countable):
- clause 3 is `|σ| ≤ |ε + Ω^σ|` (norm of the weight), not `σ ≤ …` — the same thing for countable `σ`;
- the bound `Ω^(ε+Ω^σ) < Λ` is kept once, at the bottom of the chain (`CondDown 0`), which implies all the
  inner bounds (`σ ≤ expDown k ss σ ≤ Ω^(expDown k ss σ)`).

## 2. Statements

- (OG) `GoodF (k+1) Ψ → GoodF k Φ → ∀ a, GoodF k (orbit A_{k+1} Ψ Φ a)`.
- (TG) `GoodF (m+1) B_m` for every `m`.
- (OW) `WeightF (k+1) s Ψ → WeightF k s' Φ → NormSeparated s' (s+1) → Ω^(s+1) ≤ Λ →
        ∀ a, WeightF k (s' + Ω^s·a) (orbit A_{k+1} Ψ Φ a)`.
- (TW) `WeightF (m+1) 0 B_m` for every `m` ("`B_m` has weight 0 at its own type = adds `Ω^0 = 1`").
- (AL) `∀ l ≥ 1, LevelFactsAt l ∧ PsiTowerLevelAt l`; then `AllTowerCalibration` by `exact_AllFromLevels`.

## 3. Check (a): specialization at k = 0, 1 (levels 1, 2)

- `GoodF 0 H ⟺ GoodFn H`. `GoodF 1 G ⟺ ∀ K, GoodFn K → GoodFn (G K) ∧ ∀ x, B_0 K x ≤ G K x` = `GoodOp G`.
- `WeightF 0 σ H ⟺ GoodFn H ∧ (Ω^σ < Λ → StepUp (Ω^σ) H ∧ StepLow (Ω^σ) H)` = `IsStep σ H` guarded by the bound.
- `WeightF 1 s G ⟺ GoodOp G ∧ ∀ ε H, WeightF 0 ε H → ExpSep ε s ∧ Ω^(ε+Ω^s) < Λ → step (Ω^(ε+Ω^s)) (G H)`; for
  countable `s`, `ExpSep ε s ∧ bound = ExpCond ε s`, so this is the hypothesis/conclusion shape of
  `OpWeightSuccessor`/`LevelTwoWeight`, and `levelTwoGood`/`levelTwoWeight` say `WeightF 1 e (B_1^e B_0)`.
- (TW) at `m = 0`: `IsStep ε H → ExpSep ε 0 ∧ Ω^(ε+1) < Λ → step (Ω^(ε+1)) (B_0 H)` = zero case of
  `levelTwoWeight` (`stepSuccessor`, `normPrincipal_opow`).
- (TW) at `m = 1`, flattened: `WeightF 1 s G`, `IsStep ε H`, `ExpSep s 0`, `ExpSep ε (s+1)`, bound ⟹
  step `(Ω^(ε+Ω^(s+1)), B_1 G H)` = `OpWeightSuccessor` with `e` replaced by an arbitrary weight `s`; the only
  extra hypothesis `ExpSep s 0` (`|s| ≤ |s+1|`) is automatic for countable `s`.

## 4. Check (b): the step at type `A_{m+2}`, `m = n+1 ≥ 1`, uses only lower statements + `stepDiagonal`/`stepLimit`

No induction on `m` is needed: (TG), (TW) are proved for each `m ≥ 1` by the same argument, the hereditary
hypotheses on the environment replacing the induction hypothesis.

Function side. `xs` good on slots `1..n+2`, `Ψ = xs (n+2)`, `Φ = xs (n+1)`,
`K_a := appDown n (orbit A_{n+1} Ψ Φ a) xs : A_1`. Then `appDown (n+2) B_{n+1} xs = fix (a ↦ K_a 0)`
(unfolding lemma) and the family satisfies
(F1) `K_a` good (by (OG)), (F2) `B_0 K_a ≤ K_{a+1}` pointwise (domClause of `Ψ` at `xs[n+1 ↦ orbit a]`),
(F3) `K_l` = pointwise sup at limits. From F1–F3 alone (the proofs of `LevelTwoFunctionProof` with
`orbit A_1 G H a` replaced by `K a`): monotone/strict in `a`, `a ≤ K_a 0`, fixed points of `a ↦ K_a 0` are limits,
closed under the family, critical above `Γ_0`; `D = fix(a ↦ K_a 0)` is good and `B_0 K_a x < D x` for `a < D x`
(`B_0 K_a x ≤ K_{a+1} x < D x`), which gives `domClause (n+2) B_{n+1} xs` with `a = 1`. (OG): successor by
application-closure of `GoodF` (`GoodF (k+1) F → GoodF k G → GoodF k (F G)`, using `K ≤ B_0 K`), limit by
"a pointwise sup of good functions is good".

ψ side. `xs, ss` weighted on `1..n+2`, `s = ss (n+2)`, `s' = ss (n+1)`,
`CondDown (n+2) ss 0 = ExpSep s 0 ∧ ExpSep s' (s+1) ∧ CondDown n ss (s' + Ω^(s+1))`.
1. (OW) at `k = n`: `orbit a` has weight `s' + Ω^s·a`. Successor: application-closure of `WeightF`
   needs `ExpSep (s'+Ω^s·a') s` — from `NormSeparated s' (s+1)` by `norm_leading_gen` (general `nsep_step`,
   `nsep_norm_mul`). Limit: `stepLimit` on `π_β = Ω^(expDown k ts (s'+Ω^s·β))`; its four index hypotheses for the
   base family `β ↦ s'+Ω^s·β → s'+Ω^s·l` and their transport through `ε ↦ ε + Ω^(·)` (family lifting, below).
2. `K_a` is a step at `Ω^(expDown n ss (s'+Ω^s·a))` since `CondDown` is monotone in its last argument.
3. `stepDiagonal` on `π_a = Ω^(expDown n ss (s'+Ω^s·a))`, `πΩ = Ω^(expDown n ss (s'+Ω^(s+1)))`.
   Base family `η_a = s'+Ω^s·a → s'+Ω^(s+1)`: cofinality with norm bound (leading coefficient of `τ − s'`),
   `|η_a| = max(|s'|, a, |s|) ≤ max(|s'+Ω^(s+1)|, a)` — uses `|s'| ≤ |s'+Ω^(s+1)|`, `|s+1| ≤ |s'+Ω^(s+1)|`
   (ExpSep s' (s+1)) and `|s| ≤ |s+1|` (**ExpSep s 0 — the one side condition level 2 did not show, because
   there `s` was countable**), and `|η_a| ≤ |τ|` on `[η_a, ηΩ)`.

Family lifting (stated once, used for both `stepDiagonal` and `stepLimit` families): if `ExpSep ε T` and
`ε + Ω^T < Λ` then for `η < T`: `|ε+Ω^η| = max |ε| (max 1 |η|)`; every `τ ∈ [ε+Ω^η, ε+Ω^T)` has a `ρ ∈ [η, T)` with
`max |ε| (max 1 |ρ|) ≤ |τ|`; every `τ < ε+Ω^T` has `ρ < T` (or `ρ = 0`) with `|ρ| ≤ |τ|` and `τ < ε+Ω^η` for all `η > ρ`.
Hence the three norm hypotheses pass from `(η_a → T)` to `(ε+Ω^(η_a) → ε+Ω^T)`; iterate along `expDown`, and
once more with `ε = 0` for the final `Ω^(·)`.

## 5. Level 3 on paper (the test asked for)

`l = 3`: `L_e = B_2^e B_1 : A_3`. (OW) with `Ψ = B_2` (weight 0 by (TW)), `Φ = B_1` (weight 0), `s = s' = 0`:
`L_e` has weight `0 + Ω^0·e = e`; needs `NormSeparated 0 1`, `Ω ≤ Λ`. Flattened at `towerEnv` (slots `B_0`, `N_B`
of weight 0): `CondDown 2 0 e = ExpSep 0 e ∧ ExpSep 0 (Ω^e) ∧ Ω^(Ω^(Ω^e)) < Λ`, all trivial at `ε = 0`; step
`(Ω^(Ω^(Ω^e)), (B_2^e B_1) B_0 N_B)`, i.e. `towerIndex 3 e`. Inside (TW) for `B_2`: `Ψ : A_3` of weight `s`
(here the countable `a'`), `Φ : A_2` of weight `s'`, `H : A_1` of weight `ε`; conditions
`ExpSep s 0`, `ExpSep s' (s+1)`, `ExpSep ε (s'+Ω^(s+1))`, bound. Hereditarily `s'` is *not* countable
(`Φ` ranges over orbit stages of weight `s''+Ω^t·a`), which is why every norm lemma is needed at arbitrary
exponents below `Λ`. No further side condition appears: the three clauses of `ExpSep` are exactly what the
lifting consumes at each depth, and `CondDown` monotonicity needs nothing else.

`PsiTowerLevelAt l` from the step at the empty context is `psiO_tower_two` verbatim with
`|towerIndex l e| ≤ e` (root's `exact_TowerIndexFacts`) in place of the explicit norm; the restart lemma is
leastness of `fix` at successors and monotonicity in the stage at limits.

## 6. Module plan

`ActualCalibrationUniformTargets` (defs, function-side statements) → `…UniformFamilyProof` (F1–F3 ⟹ facts) →
`…UniformGoodProof` ((OG), (TG)) → `…UniformWeightTargets` (weight defs, (OW), (TW), (AL)) →
`…UniformNormProof` (general norm calculus, lifting) → `…UniformWeightProof` → `…UniformLevelProof` →
`ActualCalibrationAllProof`.
