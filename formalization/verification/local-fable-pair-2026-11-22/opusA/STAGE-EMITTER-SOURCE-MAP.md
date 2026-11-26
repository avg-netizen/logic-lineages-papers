# Stage emitter assembly — source map (Opus A, task 4, 2026-11-22)

**Serves.** Paper 17 `thm:arithmetic` via the comparator `ClosedBlockDecision` (#1396): the computable
emitter `∃ alt, SupplierShape alt ∧ SupplierExact f B alt ∧ ∃ high, Computable high ∧ Emits alt B high`.

- `StageEmitterRowTargets`: `RenderingEffective R` (four Primrec fields, uncurried as in Fable-2's
  render effectivity statements); Primrec of `levelCode R`, `signedCode R`, `rowCode R`. (Fable-2's turn-003
  item 2; owned here.)
- `StageEmitterHighTargets`: `chartCode`/`highCode` (Fable-2's turn-003 formula: raw charts → `familyCode` →
  `properClausesCode` → `rowCode R` per row → `joinCode` → `childCode`); `ExactStageEmission`
  (`R.Exact → ∀ B, Emits levelOrder B (highCode R)`, a literal list equation for every family, no dimension or
  shape use); `ExactHighCodeEffectivity`; `ExactConditionalEmitter` (every `SelectedWithThreshold f B`);
  `ExactConditionalClosedBlockDecision` (`(∃ R, R.Exact ∧ RenderingEffective R) → ClosedBlockDecision`).
- `StageEmitterGuardTargets`: `renderingWith g := ⟨appendCode, g, linearCode, modularCode⟩`; with the gated
  `exactAppendCode`, `exactLinearCode`, `exactModularCode` and their effectivity, `GuardExact g → GuardEffective g →
  ClosedBlockDecision`.

**Assumed.** Only `GuardExact g` (verbatim the `guard` field of `Rendering.Exact`) and `GuardEffective g`.
Everything else is a gated theorem: #1398 `exactRawRowPackets`, #1404–#1408 `exactJoinCode`/`exactChildCode`/
`joinEffectivity`/`childEffectivity`/`exactAppendCode`, #1393 `exactRawProperClauses` + effectivity, #1298
`exactRawRankCalibration` + effectivity, #1311/#1336 `exactRawStageNamesAndCharts` + chart effectivity, #1397
`exactLevelOrderSupplierShape`/`…Exact`, #1396 `exactClosedBlockReduction`, Fable-2's linear/modular render keys.

**Not claimed.** Any guard program. Nothing about other suppliers.
