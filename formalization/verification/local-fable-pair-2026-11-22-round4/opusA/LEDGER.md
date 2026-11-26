# Opus A ledger — round 4

## Step 1: shared external interface
- Read root's #1463 (`ConditionalTowerCofinality`) and Opus B's round-3 `thm:upper` table (R1, R2).
- `ExternalOrdinalInterfaceTargets` frozen: sha `e040bcb1…eb81`, receipt `1795403969736168254-3288731`.
  - It reuses root's `CollapseData` / `TowerHypotheses` for E2.
  - It adds `Calibration` (E1, against #1462's `sequenceValue`), `BHIdentification` (E3) and `UpperBound`.
  - Values are `Ordinal.{0}`; the index order is abstract.
- `EXTERNAL-INTERFACE.md` was written immediately after.
- E4 and R1 went into `ExternalOrdinalInterfaceID1Targets`, because their vocabulary has a closure of about 700
  modules.
  - First compile failed on a missing Mathlib ordinal import (`…4138040128796-3290042`).
  - Frozen: sha `8e6ed85d…c6e3b`, receipt `1795404149778390897-3290098`. The doc was updated with it.

## Step 2: conditional thm:height
- `ConditionalHeightTargets` frozen: sha `35cd1d59…4274`, receipt `1795404223726135807-3290467`.
- `ConditionalHeightProof` **PASS** on the first gate, `1795404261857473158-3290689`: `conditionalHeight`, standard
  axioms, peak 949,780 KiB.
- Bookkeeping was proved, not assumed: `restrictedRankLe` (from #1448), `nativeHeightLe`, `heightLeOfUpper`,
  `lowerBound`.
- Wrote `CONDITIONAL-HEIGHT-SOURCE-MAP.md` and `CONDITIONAL-HEIGHT-EVIDENCE.json`.
