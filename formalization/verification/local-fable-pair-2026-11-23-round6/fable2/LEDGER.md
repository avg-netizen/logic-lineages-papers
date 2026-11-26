# Fable-2 ledger — round 6

## H02 — existence

- 2026-11-22T23:51:48-06:00 — targets frozen before any proof text exists.
  - module `LogicLineages.PersistentMarking.ConditionalCollapseExistenceTargets`
  - file `LogicLineages/PersistentMarking/ConditionalCollapseExistenceTargets.lean`
  - sha256 `59536f74302447216d0e1f06cbcb47a43759ed1a967316113952559ddfb4520e`
  - defs: `Solvable`, `SolvableBelow`, `CharacterizationExists`, `CharacterizationExistsBelow`,
    `SolvableIffSolvableBelow`
- 2026-11-22T23:52:08-06:00 — proof gated, first attempt, no failed drafts.
  - module `LogicLineages.PersistentMarking.ConditionalCollapseExistenceProof`
  - sha256 `42d2243c5f0603b4f3908056471a5cd35935b2ae9a8c0e423906ed79afc8eeaa`
  - targets sha256 unchanged (`59536f74…b4520e`)
  - gate: `COMPILE_PASS` for both modules, receipt `build-reports/1795413122950914125-3313037.json`
  - theorems: `characterizationExists`, `characterizationExistsBelow`, `solvableIffSolvableBelow`
  - axioms: `[propext, Classical.choice, Quot.sound]` for the two existence theorems; `[propext]` for the
    equivalence
  - device: `WellFounded.fix` + `WellFounded.fix_eq` on the index; `WellFounded.has_min` on the values
  - finding: the dependent `SolvableBelow` is equivalent to `Solvable`, so it is not a sharper hypothesis
  - evidence: `COLLAPSE-EXISTENCE-EVIDENCE.json`, `COLLAPSE-EXISTENCE-SOURCE-MAP.md`
