# External ordinal interface (Opus A, round 4)

**Frozen:** `LogicLineages/NativeModule/PersistentMarking/ExternalOrdinalInterfaceTargets.lean`
- sha256 `e040bcb11a3988d7c26c72b86c0957f5c790e6d00d6a00a1a5a34fcc4c43eb81`; compiled alone, receipt
  `1795403969736168254-3288731`.
- Namespace `LogicLineages.PersistentMarking.ExternalOrdinalInterfaceTargets`.
- Imports: `NativeTowerSequenceTargets` (#1462), `NativeRankTargets` (#1448), and root's
  `ConditionalTowerCofinalityTargets` (#1463).
- Nothing is defined concretely and nothing is asserted.

**Value and index orders.**
- Values are `Ordinal.{0}`: ranks of terms, `Δ_n'`, `ψ_B(a_n)` and `BH` are all countable ordinals.
- The collapse index order `I` (where the Ω-based `a_n` and `Λ = ε_{Ω+1}` live) is abstract, with `[LinearOrder I]`.
- The collapse data is root's `CollapseData I Ordinal.{0}` (#1463).

```lean
-- E2 (P) and the other printed inputs of lem:tower-cofinality: root's #1463, reused verbatim
--   ConditionalTowerCofinality.CollapseData I O  (psi norm critical one endpoint a)
--   ConditionalTowerCofinality.TowerHypotheses D (characterization increasing below cofinal
--                                                 normBound criticalAboveOne criticalSup)

def Calibration (D : CollapseData I Ordinal.{0}) : Prop :=                       -- E1
  ∃ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul ∧ OmegaArithmeticEquations Z s mul w one pow fix ∧
    ∀ n, (sequenceValue fix pow w n).val = D.psi (D.a n)

def BHIdentification (D : CollapseData I Ordinal.{0}) (BH : Ordinal.{0}) : Prop :=  -- E3
  D.psi D.endpoint = BH

def UpperBound (BH : Ordinal.{0}) : Prop :=                          -- thm:upper conclusion
  ∀ S (wf : WellFounded (fun t s : Expr => ConfinedPair.Strict S s t)) (q : Expr) (τ : Ty),
    PaperTerm S q τ → Ordinary q → confinedRank (wf.apply q) < BH
```

## What each declaration stands for

| Declaration | Printed sentence or citation |
|---|---|
| `Calibration D` (E1) | (D) "satisfies Δ_n = ψ_B(a_n) by the cited calibration" (Simmons 2004 Thm 6.1 / Cor 6.2, 2008 Thm 5.10, the identity after 2008 Lemma 6.6, and the tameness paragraph). `sequenceValue` is the paper's own composite `Δ_n'` (#1462). Stated for *some* solution of the arithmetic and ω equations, the weakest form `thm:height` uses. |
| `TowerHypotheses D` (E2, from #1463) | (P), Simmons 2004 §5; "`|a_n| ≤ 1`"; "every value in the critical base sequence is at least Γ_0 > 1"; "these criticals are closed under countable increasing suprema"; `Λ = sup_n a_n` |
| `BHIdentification D BH` (E3) | "The Veblen-hull endpoint ψ_B(ε_{Ω+1}) is the BH of the inductive-norm calibration" (Pohlers §§9.4–9.5) |
| `UpperBound BH` | `thm:upper`, second conjunct: "rk_⊐(s) < BH for every ordinary term s". This is the shared form; Opus B proves it from E4 + R1. |

## Second module: E4 and R1 (proposal for Opus B)

**Frozen:** `LogicLineages/NativeModule/PersistentMarking/ExternalOrdinalInterfaceID1Targets.lean`
- sha256 `8e6ed85d920e9e2c92bc7bb79f97bec60a52aac0243adc6e33cc8ae6833c1c3b`; receipt `1795404149778390897-3290098`.
- Namespace `LogicLineages.PersistentMarking.ExternalOrdinalInterfaceID1Targets`.
- Imports: `ID1Completion.SourcePresentationDefinitions`, the twin `NumberedWindowExternalIDStages`,
  `Mathlib.SetTheory.Ordinal.Rank`. The closure is about 700 modules, which is why these two live in their own module.

```lean
def bodyOperator (B : Positive (Fin 1)) : Operator := fun P n => realize P B.formula ![n]

def NormTheorem (BH : Ordinal.{0}) : Prop :=                                       -- E4
  ∀ (B : Positive (Fin 1)) (n : Nat),
    Nonempty (Derivation B [] (Positive.predicate (α := Empty) (numeral n)).formula) →
    ∃ a < BH, stage (· < ·) Ordinal.lt_wf (bodyOperator B) a n

def InternalAccessibility (d : Data) (context : Nat) : Prop :=                      -- R1
  Nonempty (Derivation (sourceBody d context) [] (allTermsFormula d context))
```

| Declaration | Printed sentence or citation |
|---|---|
| `NormTheorem BH` (E4) | `thm:upper`: "Applying the published norm theorem yields rk_{R_S}(tr s) < BH" (Pohlers Defs 6.3.1, 6.3.5, 9.1.2; Lemma 6.5.2; Thms 9.5.5–9.5.6). It is stated for every positive body and every numeral atom; stages are the repository's `stage` of the body's realize-operator. |
| `InternalAccessibility d c` (R1) | `thm:upper`: "The arithmetic accessibility proof supplies an ID₁ proof of the individual I-membership of tr(s)". This is the uniform form, `lem:arithmetic-accessibility`. It is internal, not external. |

Opus B may restate E4/R1 in its own Targets, for example over tagged atoms `tagTerm false (numeral n)`. Two bridges
are still Opus B's to supply: from the realize-operator of `sourceBody` to `taggedStep S K`, and from the window to
`(d, context)`.
