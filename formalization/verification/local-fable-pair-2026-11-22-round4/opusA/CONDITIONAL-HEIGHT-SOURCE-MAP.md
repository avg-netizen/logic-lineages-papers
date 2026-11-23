# CONDITIONAL-HEIGHT: source map (Opus A, round 4)

Paper 16 `thm:height` (ordinals.tex 634–643), compiled conditionally on the external interface.

## Gated

| Module (`LogicLineages/NativeModule/PersistentMarking/`) | sha256 | Receipt |
|---|---|---|
| `ExternalOrdinalInterfaceTargets` (frozen) | `e040bcb11a3988d7c26c72b86c0957f5c790e6d00d6a00a1a5a34fcc4c43eb81` | `1795403969736168254-3288731` |
| `ExternalOrdinalInterfaceID1Targets` (frozen; E4/R1 proposal) | `8e6ed85d920e9e2c92bc7bb79f97bec60a52aac0243adc6e33cc8ae6833c1c3b` | `1795404149778390897-3290098` |
| `ConditionalHeightTargets` (frozen) | `35cd1d592134e2d39cb14631d5ee8a558e249021522c5c74f952290040324274` | `1795404223726135807-3290467` |
| `ConditionalHeightProof`: `conditionalHeight : ConditionalHeight` | `a4a2a5ad02261ced49522b490a7300f76bc564bf1b9d03265af2edd1e38a1300` | `1795404261857473158-3290689` (702 modules, all rc 0) |

- Axioms: `[propext, Classical.choice, Quot.sound]`.
- Peak RSS: 949,780 KiB at `ConditionalHeightProof`, against a cap of 1,572,864 KiB.

**Statement.** Take any linear index order `I`, any `CollapseData I Ordinal.{0}` (#1463) and any `BH : Ordinal.{0}`, and
assume:
1. `Calibration D` (E1);
2. `TowerHypotheses D` (E2: (P), plus the printed tower facts);
3. `BHIdentification D BH` (E3);
4. `UpperBound BH` (the `thm:upper` conclusion).

Then for every signature `S`:
- `descendingHeight S = BH`, where this is `⨆` over ordinary terms of `rank + 1` in the full confined strict relation;
- `nativeHeight S = BH`, where this is `⨆` over closed native terms of type σ = o→o of `rank + 1` in their restriction.

## Printed text against the Lean

| Printed | Lean | Source |
|---|---|---|
| "The descending height of ⊐ is BH" | `descendingHeight S wfFull = BH` | definition (Targets) |
| "already cofinally witnessed by closed native T terms of outer type o→o" | `nativeHeight S wfNative = BH` | definition (Targets) |
| "The realizers (R)" | `towerRanks`: `ψ(a_n) ≤ r_σ(t_n)` | #1462 (`exact_NativeTowerSequenceRealization`) plus E1 |
| "and Lemma tower-cofinality" | `conditionalTowerCofinality` | #1463, from E2 and E3 |
| "give the lower bound for the restriction to closed native terms" | `lowerBound`: `BH ≤ nativeHeight` | proved: `BH = ⨆ ψ(a_n) ≤ ⨆ (r_σ(t)+1)` |
| "Its ranks are bounded by the ranks in the full ordering" | `restrictedRankLe`, `nativeHeightLe` | #1448 (`exact_ActualClosedNativeRanks`), plus proved: closed native terms are ordinary |
| "Theorem upper bounds each individual full rank below BH" | hypothesis `UpperBound BH` | Opus B's conditional `thm:upper` |
| "Taking the supremum of ranks plus one gives equality" | `heightLeOfUpper`, `le_antisymm` | proved |
| "No individual term has been assigned rank BH" | a remark; consistent with `UpperBound` (every rank < BH) | — |

## Hypothesis list of `conditionalHeight`
- **`Calibration D`** (E1, Simmons). The paper's `Δ_n'` equals `ψ(a_n)` for some solution of the arithmetic and ω equations.
- **`TowerHypotheses D`** (E2, the inputs of #1463):
  - (P), from Simmons 2004 §5;
  - `a_n` increasing, below `Λ`, and cofinal in `Λ`;
  - `|a_n| ≤ 1`;
  - critical values exceed 1;
  - the lub of a strictly increasing sequence of critical values is critical.
- **`BHIdentification D BH`** (E3, Pohlers §§9.4–9.5).
- **`UpperBound BH`** (the conclusion of `thm:upper`; Opus B derives it from E4 + R1 in `ExternalOrdinalInterfaceID1Targets` or its own restatement).

## Findings about the printed text
1. **Inputs used beyond (P) and the norm bound.** The cofinality step uses three facts that the paper asserts in its
   own text without proof or citation-level precision. They come in through #1463's `TowerHypotheses`, and my round-3
   list did not name them separately:
   - "These criticals are closed under countable increasing suprema" (l. 597–598);
   - "every value in the critical base sequence is at least Γ_0 > 1" (tameness paragraph);
   - the order facts on `a_n` and `Λ = sup_n a_n` (by definition, but about Ω-ordinals outside the countable layer).

   All three belong to the external Simmons setting, so they are external, not new mathematics.
2. **Field of "⊐".**
   - The proof works for the height over **ordinary terms**, because `thm:upper` bounds only those ranks. I state the
     height over the ordinary terms of each signature.
   - If "descending height of ⊐" were meant over a larger field (for example, marked comparison terms), the printed
     proof would need a bound for those ranks, and `thm:upper` does not give one. This is a reading point for the owner.
3. **The thm:height proof needs nothing else.** Beyond E1–E3, `thm:upper` and the compiled parts, the printed proof of
   `thm:height` uses no hypothesis. "Restricted rank ≤ full rank" was already compiled (#1448). The height/supremum
   bookkeeping is proved here.
