# K2 `FreshSeedLeast` — source map for `Paper16AccessibilityMilestoneFreshSeedLeastTargetsV2`

Fable B2, 27 November 2026. Module
`LogicLineages/NativeModule/PersistentMarking/Paper16AccessibilityMilestoneFreshSeedLeastTargetsV2.lean`
(definitions only; sha256 in `LEDGER.md`).

**Serves.** Paper 16 `lem:arithmetic-accessibility`, the type split at arrow types
(`CarrierTypingCases`), through `FreshApplicationTotal` = K1 ∧ K2
(`fableB/FRESH-APPLICATION-REPORT.md`). K2 is the already frozen
`…FreshApplicationTargetsV2.FreshSeedLeast`; nothing in that file changes.

**Definitions.**

- `SeedLeastOnJoinedWindow` — K2 from the installed code. For any `InstalledWindow S K W`, settings
  `s` and programs `X base T V baseM`: if `A.scalar` is the finite filter over the address scalar of
  `joinedAuxiliaryWindow s base Tg V A.typeGuard baseM`, `A.least = memoFilteredLeast C Base s`
  (`C = measuredStrictCover V A.typeGuard baseM`, `Base = joinedBiAuxBase …`), and the two open
  laws `MemoSelectedReports C s Base`, `OpenRankTypeGuards W Tg A.typeGuard` hold, then
  `FreshSeedLeast A c` for every `c`.
  *Assumed:* two equations between installed programs and two open-term laws, all four provided by
  the packet `exact_ConcreteLambdaJoinedMemoPacketAt` for the selected window.
  *Not assumed:* anything about the application seed (no least report, no window, no coverage, no
  syntax acceptance of the seed), no numeric calibration of `T`, `V`, `baseM`, `base`.
- `LambdaWindowWithGuards` — `…WindowWithLeastTargetsV2.LambdaWindowWithLeast` with one more
  conjunct `OpenRankTypeGuards (sourceWindow K) Tg A.typeGuard`. A restatement: the packet proves
  the conjunct and the earlier restatements drop it. It is needed because `T` is existentially
  bound in the selection, so no fact about it can be recovered afterwards.
- `LiteralWindowWithSeedLeast` — `…WindowWithLeastTargetsV2.LiteralWindowWithLeast` with that
  conjunct, with `FreshSeedLeast A c` asserted for the selected window, and with the first
  reduction weakened to `FreshAddressCarrier A c → CarrierTypingCases A c`.

**Not claimed.** K1 `FreshAddressCarrier`; `TypedCarrierComputability`; `AllTerms`;
`lem:arithmetic-accessibility` itself. The window of `LiteralWindowWithSeedLeast` is produced by
the same construction as the window of `exact_LiteralWindowWithLeast`, but it is a new existential
statement: it does not assert K2 for "the" window an earlier theorem's proof chose (two
existential eliminations cannot be identified), it supersedes that selection.

**Why K2 needs no new induction.** The auxiliary-node introduction laws
`EXPLICIT-COVER-SCOPE.md` lists as "not written" exist in the legacy tree:
`exact_OpenUnitAuxSyntaxIntro` (syntax wrapper accepts an auxiliary node with accepted children),
`exact_OpenSelectedGrammarAuxScratchMeasured` (the explicit generator lists it), both consumed by
`exact_OpenStrictMeasuredAtScratch` → `exact_OpenStrictMeasuredParentWindow` →
`exact_OpenJoinedAuxiliaryParent`. The sealed half of the joined window carries
`coverageReport C s ctx seed`, and `exact_OpenLeastOnFromCoverage` turns a coverage report into a
least under `packedLeastOn C E s` for any edge program `E`.
