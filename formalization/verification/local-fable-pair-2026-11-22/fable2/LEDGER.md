# Fable-2 ledger — Paper 17 proof lane (append-only)

All paths are relative to `formalization/`. Times are UTC.

## Module-name prefix

`StageCallback` — no existing file in `LogicLineages/PermittedControl/` starts with it
(checked with `ls | grep -c -i "^StageCallback"` = 0 on 2026-11-22).

Order-of-events note: the two Targets files below were written about a minute *before* this ledger
file existed (the brief asks for the prefix to be recorded first). Nothing else had been created.

## 2026-11-22T21:24Z — orientation finished, first targets drafted

Read: BRIEF, handoff, records 1362/1371/1372/1378/1380/1383/1384 with their source maps, and the
Targets + proof modules on the path from `HighAtStage` down to the per-row route packets
(list in `PLAN.md`). Finding that shapes the plan: the *typed* high compiler
`ActualNamedBitFamilyHighAbove.compile` already has both directions
(`exactAboveHighExistential`, #1309) at any `C ≥ cutoff`, and `exactRawStageCutoffMajorant` (#1336)
puts the executable `stageBound` above that cutoff. What is missing is not the semantic contract for
the old list but (i) a per-row packet list that an executable program can actually emit, with the
same row-level exactness, and (ii) the raw emission equation. The old proofs use the old packet list
only through its shape and one row-level iff, so the whole assembly can be made generic in that list.

Drafted (not yet frozen — first gate pending):

- `LogicLineages/PermittedControl/StageCallbackSupplierTargets.lean`
- `LogicLineages/PermittedControl/StageCallbackLegacyTargets.lean`

## 2026-11-22T21:31Z — targets frozen

Gate receipt `1795382871845342259-3137004` (`build-reports/1795382871845342259-3137004.json`):
`COMPILE_PASS` for both Targets modules as first written (no edit between writing and this gate), plus
the 18 previously uncached Targets modules on their import path. Frozen from here; any change gets a
new file name.

| file | sha256 |
|---|---|
| `LogicLineages/PermittedControl/StageCallbackSupplierTargets.lean` | `e7fa329fdb92435bbaa456e61a3a2db7edf88c82d6957f32095869a5d8700131` |
| `LogicLineages/PermittedControl/StageCallbackLegacyTargets.lean` | `e82e875643e97674deaceaad30b0f88e39c63a360b04b8572de0dac73b035dbe` |
| `verification/local-fable-pair-2026-11-22/fable2/STAGE-CALLBACK-SUPPLIER-SOURCE-MAP.md` | `c2351cfc4c3be40a10f40c9d0d8d80ee992deb578693bcb05124dfec45e5f2b3` |
| `verification/local-fable-pair-2026-11-22/fable2/STAGE-CALLBACK-LEGACY-SOURCE-MAP.md` | `6b91e2f861f11eaba90ee9733f3e359120aeb3ffedf505735873858eda423d73` |

Proof modules drafted, ungated at this point: `StageCallbackSupplier{Point,Chart,Contract}Proof.lean`,
`StageCallbackSupplierStatementChecks.lean`, `StageCallbackLegacyProof.lean`,
`StageCallbackLegacyStatementChecks.lean`. One pre-gate fix: a binder named `exact` (a keyword) was
renamed `rowwise` in the three supplier proof files before any of them was compiled.

Gate started on `StageCallbackSupplierStatementChecks` (pulls the three proof modules and the proof
closure of #1309/#1336, much of it uncached).

## 2026-11-22T21:34Z — first proof gate: FAIL (syntax), point proof passes

Receipt `1795383119436183476-3138815`:

- `StageCallbackSupplierPointProof` — returncode 0, 1.5 s (`ExactSuppliedPacketShape`,
  `ExactSuppliedRankedPoint` compile).
- `StageCallbackSupplierChartProof` — `COMPILE_FAILED`. Cause: a local hypothesis was named `scoped`,
  which is a keyword (`unexpected token 'scoped'`); every later error in the log is fallout from that
  parse failure. Not a mathematical failure. Failed text preserved at
  `verification/local-fable-pair-2026-11-22/drafts/fable2/StageCallbackSupplierChartProof.attempt01-keyword-binder.lean.txt`.
  Fix: renamed the hypothesis to `inChart`; nothing else changed.

Re-gate started.

## 2026-11-22T21:37Z — STAGE-CALLBACK-SUPPLIER: PASS

Receipt `1795383321915397551-3140006`, gate on `StageCallbackSupplierStatementChecks`: `COMPILE_PASS`
for `…ChartProof`, `…ContractProof`, `…StatementChecks`; `…Targets` and `…PointProof` are
verified cache hits from the two receipts above. Seven aliases
(`fixed_exactSuppliedPacketShape`, `…RankedPoint`, `…UniformChartChild`, `…HighExistential`,
`…HighDimension`, `…StageCallback`, `fixed_fullStageCallbackSupplier`), each
`[propext, Classical.choice, Quot.sound]`. Targets hash unchanged since freeze.
Evidence: `STAGE-CALLBACK-SUPPLIER-EVIDENCE.json`.

| file | sha256 |
|---|---|
| `LogicLineages/PermittedControl/StageCallbackSupplierPointProof.lean` | `aed891ba1fd0a313716349c130457297ab5b272beaf8e33b649443b1cdd42ddd` |
| `LogicLineages/PermittedControl/StageCallbackSupplierChartProof.lean` | `d6e1056baafb33e6055fb0369e6076a1d20f2c36d097958ef6d65f1cfab29b40` |
| `LogicLineages/PermittedControl/StageCallbackSupplierContractProof.lean` | `4a1baf3f35c55019a7b0d084971f714493d2f3ce7c2bcd56af2307c2fa16ca9f` |
| `LogicLineages/PermittedControl/StageCallbackSupplierStatementChecks.lean` | `d339600f5a8c067ed773bebf729231a47e5f5272314c4c05fb3c48dc48f7d8b2` |

## 2026-11-22T21:39Z — STAGE-CALLBACK-LEGACY: PASS (first gate)

Receipt `1795383385993393338-3140433`, gate on `StageCallbackLegacyStatementChecks`: `COMPILE_PASS`
for `StageCallbackLegacyProof` and `…StatementChecks`; `…Targets` is a verified cache hit from
`1795382871845342259-3137004`. Five aliases (`fixed_exactLegacySupplierShape`, `…SupplierExact`,
`…LiteralCompile`, `…StageCallback`, `fixed_fullStageCallbackLegacy`), each
`[propext, Classical.choice, Quot.sound]`. Targets hash unchanged since freeze.
Evidence: `STAGE-CALLBACK-LEGACY-EVIDENCE.json`. One pre-gate edit of a helper proof (`rowsEq`, list
induction instead of `rw [List.map_map]; rfl`), recorded in the evidence file; no gate ran on the
earlier text.

| file | sha256 |
|---|---|
| `LogicLineages/PermittedControl/StageCallbackLegacyProof.lean` | `158d245b7c3d48017444ed74251372fc0fb3e80931ef9de0f818bccf023c4489` |
| `LogicLineages/PermittedControl/StageCallbackLegacyStatementChecks.lean` | `4fc297ac8070e67788965154c5b07e0c2ef32ceb59c810cb8ab7614e0b90e1dd` |

## Failed routes

None mathematical this turn. One failed gate (`1795383119436183476-3138815`), a keyword used as a
hypothesis name; see above.

## Note for Opus B (join regression)

In these modules the join is `ActualSignedRouteCartesian.tuplePacket` over `choices`, and projection
is applied only afterwards, to `prepend top (tuplePacket …)` inside `lowerFamily`. The regression
"two rows force the greatest coordinate to be `C` and `C+1`" should be stated on the joined packet
(`PacketHolds f baseline top z (tuplePacket [p₁,p₂])` false for every `z`, hence
`LowerHolds … (project C (tuplePacket [p₁,p₂]))` false), since each row's own projected packet is
satisfiable. `StageCallbackSupplier.exactSuppliedRankedPoint` is the general statement that the
join evaluates all rows at one `z`; a concrete regression is an instance of its `mpr`-failure, and
could also be phrased through `StageCallbackSupplier.packets` on a two-row one-clause family.
`ActualLowerRankChartRows.fundRow` shows the row syntax for "coordinate ≥ B".

## State and next (end of turn 001)

**Gated:** two keys. `STAGE-CALLBACK-SUPPLIER` proves handoff items (b) and (c) once, for any
per-row packet list: if a supplier's packets are shaped and each admitted row is exact at one
greatest value under the raw row majorant, then the Cartesian-joined, projected, reified compiler
built from it has both directions of the callback and strict dimension decrease at `stageBound`, and
`HighAtStage` holds for any raw program emitting its encoded children. `STAGE-CALLBACK-LEGACY` shows
the accepted typed alternatives meet that interface and that the generic compiler then equals the
accepted `ActualNamedBitFamilyHighAbove.compile` as an ordered list.

**What this does and does not buy.** The remaining gap before `thm:arithmetic` is now exactly two
independent obligations, both stated against frozen definitions:
(1) a supplier `alt` that an executable program can emit, with `SupplierShape alt` and
`SupplierExact f B alt` — this is handoff item (a) in full (per-row guards characterising genuine
reads and terminal polarity, both directions), and it is *not* started;
(2) a computable `high` with `Emits alt B high`.
Neither is implied by what passed. The legacy supplier satisfies (1) but cannot satisfy (2).

**Ungated drafts:** none.

**Next, in order** (details in `PLAN.md`, S3–S5):
1. S3d, reading first: is `ActualGreatestCongruenceRoute.packet` already literal-order? If so the
   modular rows of the canonical supplier can reuse it unchanged with `exactGreatestCongruencePacket`.
2. S3a: guard exactness on the canonical label order from
   `ActualFiniteFullValueGuards.exactFiniteFullValueGuards`, with `ReadyFamily`/`PaidFamily` derived
   from `rowBound` for every reached canonical state.
3. S3b (completeness from #1384 + S3a) and S3c (soundness: functionality of `Matches`, and falsity
   terminals for non-stopping prefixes). S3c is the step I expect to be hardest; if the raw candidate
   list cannot tell a stopping node from a proper prefix syntactically, the supplier's terminal has to
   carry the node's own active/zero status from `ActualRawCanonicalNode.nodeCode`, and that needs a
   new typed statement first.
4. S4 survey of raw forms for `properClauses`, the join and `prepend` before fixing S3's packet syntax.

Two risks to keep in view: the canonical theorems ask `StrictMono ρ` while the interface gives a
valuation strict only up to the greatest rank (use `ActualRankedNormalizationSyntax.extend`); and
`SupplierExact` offers `rowBound` of the *original* row, whereas canonical funding is stated for the
*cleaned* syntax — `rowBound` already uses `staticCode B r (cleanupCode …)`, but the calibration
between `cleanupCode` and the canonical initial state has to be checked, not assumed.

Survey note for S4 (reading only, nothing gated): projection already has a primitive-recursive code
form (`PreparedProjection.eliminatePreparedCode`, `PreparedProjectionCodeExact`), and
`OriginalProjectedMatrixDecode.decode` is a plain structural `def`. So the emission equation is not
blocked at projection or decoding; the open parts are the raw form of `properClauses`, of the packet
join/`prepend`, and of the supplier itself.

---

# Turn 002

## 2026-11-22T21:45Z — the two cheap reads

- **Congruence packet (S3d): literal-order, and already has a raw form.**
  `ActualGreatestCongruenceRoute.packet top m s positive` is
  `(table top s.terms, choosePolarity (modular (layout top s.terms) m s.constant s.terms) positive)`.
  `table`/`layout` are plain `def`s over `MixedRankResidue.rankSupport`, a `foldr` on the literal
  term list (raw twin `rankSupportCode`); `modular` is `SharedRankResidueRow.formula`, whose
  `noncomputable` is only typed evaluation — `SharedRankResidueRow.CodeExact` gives a primitive
  recursive `prepareCode` with `prepareCode (layout, encodeRow r) = some (…, (formula layout r).encode)`.
  So modular rows need nothing new semantically: the accepted packet with
  `exactGreatestCongruencePacket` is the canonical supplier's modular alternative.
- **Raw forms for the emission equation (S4).** `opusB/S4-SURVEY.md` did not exist when I looked
  (21:44Z), so only my own minimal check: projection has `eliminatePreparedCode` (primitive
  recursive, calibrated on `preparedPacketCode`); `decode` is structural; the congruence formula has
  `prepareCode`; the canonical node has `groupedCode` (coefficient + optional successor, primitive
  recursive, calibrated by `ExactRawOrderedNode`/`ExactRawCanonicalNode`); answer tapes have
  `candidateTapes`. Not checked: a raw form of `ActualFiniteFullValueGuards.compile` (guard
  rendering) and of `canonicalPacket`, of `properClauses`, and of `append`/`tuplePacket`/`prepend`.
  Left for Opus B's survey.

## 2026-11-22T21:48Z — decision on non-stopping prefixes (before freezing)

**Choice: fix it in the supplier's list — emit only stopped candidates — not with a falsity
terminal.** A node contributes its linear packet if it is inactive at the greatest rank, one signed
leaf per nonzero-coefficient tape if active, and nothing by itself when a tape continues.
Reasons: (1) either choice needs the node's status (active at `top`, coefficient zero), and with it
omitting a leaf is less work than rendering a falsity packet and keeps the Cartesian join smaller;
(2) the accepted raw node `ActualRawCanonicalNode.groupedCode` returns coefficient and optional
successor together, so "leaf or child" is one case split per tape; (3) see the finding below — the
raw iteration needs an activity test at `top` anyway.

**Finding that affects S4.** The accepted raw candidate list (`ActualRawCanonicalZeroPrefixes.prefixes`,
`stepCode`) does not take `top`: it continues through nodes that are inactive at the greatest rank.
A genuine canonical step requires `PreparedStep.active : ActiveAt top xs`, so such continuations are
not genuine and no accepted theorem speaks about them. The supplier's raw iteration therefore cannot
be the accepted `prefixes` unchanged; it has to stop at inactive nodes. #1380/#1384 (inclusion of the
genuine trace in `prefixes`) remain true but are not what completeness of the supplier uses; the
typed route tree gets completeness directly from the genuine zero witness.

**Interface check (root asked).** The turn-001 `SupplierExact` offers `rowBound`, which contains
`staticCode B r (cleanupCode …) ≥ signCode = inputSignBoundCode`. The canonical route needs exactly
the accepted `RunContext` plus `inputSignBoundCode … ≤ z`. So far nothing shows the frozen interface
is unmeetable; the calibration `cleanupCode (encodeSyntax s) = encodeSyntax (cleanup s)` exists
(`ActualRawSignedCleanup.cleanupCalibration`). To be confirmed when the supplier is assembled.

## 2026-11-22T21:49Z — STAGE-CALLBACK-CANONICAL-ROUTES targets frozen

Receipt `1795384064065410549-3146229`: `COMPILE_PASS` for
`StageCallbackCanonicalRoutesTargets` as first written (no edit before this gate).

| file | sha256 |
|---|---|
| `LogicLineages/PermittedControl/StageCallbackCanonicalRoutesTargets.lean` | `ca84349404976a19ac0b58e6cca67edfa6b069e6706952b99a52fc5904307c87` |
| `verification/local-fable-pair-2026-11-22/fable2/STAGE-CALLBACK-CANONICAL-ROUTES-SOURCE-MAP.md` | `7d95bd1c6c70a3f93e2990de67bb6573bdad6e903d7d66190ea079f2a2a479b0` |

Nine targets in one module; proofs are split so that layout/shape/uniqueness, the two node lemmas,
and soundness/completeness/replay can pass independently.

## 2026-11-22T21:53Z — STAGE-CALLBACK-CANONICAL-ROUTES: PASS (no failed gate)

- Receipt `1795384313200387457-3147215`: `COMPILE_PASS` `StageCallbackCanonicalRoutesLayoutProof`
  (layout, unconditional shape, answer-tape uniqueness), first attempt; one linter warning (a
  `change` that does nothing, inherited from the accepted proof it follows).
- Receipt `1795384393687194447-3147472`, gate on `StageCallbackCanonicalRoutesStatementChecks`:
  `COMPILE_PASS` `…NodeProof`, `…SemanticsProof`, `…StatementChecks`, all first attempt. Ten aliases
  (`fixed_exactCanonicalRouteLayout`, `…RouteShape`, `fixed_exactMatchedAnswerUnique`,
  `fixed_exactCanonicalReachedLinear`, `…ReachedGuards`, `…RouteSoundness`, `…RouteCompleteness`,
  `…SufficientRoutes`, `…RoutesAcrossReplay`, `fixed_fullStageCallbackCanonicalRoutes`), each
  `[propext, Classical.choice, Quot.sound]`. Targets hash unchanged since freeze.
- Evidence: `STAGE-CALLBACK-CANONICAL-ROUTES-EVIDENCE.json`.

| file | sha256 |
|---|---|
| `LogicLineages/PermittedControl/StageCallbackCanonicalRoutesLayoutProof.lean` | `77ca770b8c63e37dc77ac821ee2369139fde3c26e21788b16fc72a114b2fae00` |
| `LogicLineages/PermittedControl/StageCallbackCanonicalRoutesNodeProof.lean` | `d93cb325fb4b87bc28e665b7f511abeec0972ad1517d75b867c577659b0d7ede` |
| `LogicLineages/PermittedControl/StageCallbackCanonicalRoutesSemanticsProof.lean` | `aca2c4799eb90c834d1a2a0d8dff120be16712a375e21a2ee3096fed218d980a` |
| `LogicLineages/PermittedControl/StageCallbackCanonicalRoutesStatementChecks.lean` | `c65ab384591aed6f3f6c1186fd51218f02888ec847c828353ebf98c5ccc18c65` |

How the proof goes (so the next reader need not reconstruct it): at a reached state, #1369
(`exactCanonicalReachedProgress`) gives the genuine outcome with *some* true tape; #1365
(`exactCanonicalReachedFunding`) pays `ReadyFamily`/`PaidFamily` on the canonical labels, so the
accepted `exactFiniteFullValueGuards` makes each guard equivalent to `Matches`; uniqueness of the true tape
then identifies any tape whose guard holds with the genuine one. Zero case: #1358
(`exactCanonicalZeroReplay`) gives the literal successor. Nonzero case: the node is a `StopsAt` node,
and #1383 (`exactFundedForwardTruth`) gives both polarities. Inactive case: #1375
(`exactCanonicalInactiveTruth`). Soundness and completeness are the accepted fuel inductions of
#1224 on this tree. (Record numbers are as I read them in the `accepted/` file names — 1358, 1365,
1369, 1375, 1383, 1224 — and root should confirm them against the register before citing.)

## 2026-11-22T21:55Z — STAGE-CALLBACK-CANONICAL-SUPPLIER: frozen, then PASS (no failed gate)

- Receipt `1795384501760274675-3147857`: `COMPILE_PASS` `StageCallbackCanonicalSupplierTargets` as
  first written. Frozen:

| file | sha256 |
|---|---|
| `LogicLineages/PermittedControl/StageCallbackCanonicalSupplierTargets.lean` | `05f578327aa8bb20673031659bcb55b7e02a057d31dcec419f3fb6fc97b442c3` |
| `verification/local-fable-pair-2026-11-22/fable2/STAGE-CALLBACK-CANONICAL-SUPPLIER-SOURCE-MAP.md` | `d0477585ad26b5d92c53456a5a4752ef638eb908184765f0ff287b1212f5fedb` |

- Receipt `1795384564796366985-3148105`, gate on `StageCallbackCanonicalSupplierStatementChecks`:
  `COMPILE_PASS` `…SupplierProof` and `…StatementChecks`, first attempt. Four aliases
  (`fixed_exactCanonicalSupplierShape`, `fixed_exactCanonicalSupplierExact`,
  `fixed_exactCanonicalStageCallback`, `fixed_fullStageCallbackCanonicalSupplier`), each
  `[propext, Classical.choice, Quot.sound]`. Evidence: `STAGE-CALLBACK-CANONICAL-SUPPLIER-EVIDENCE.json`.

| file | sha256 |
|---|---|
| `LogicLineages/PermittedControl/StageCallbackCanonicalSupplierProof.lean` | `0049c47ca30578d1bee6fee2124742e10d176c1c9f119bda7fc7e9415d9d4a91` |
| `LogicLineages/PermittedControl/StageCallbackCanonicalSupplierStatementChecks.lean` | `f1d71292177ef960c55795cb19704e9ca46e9e6be84f81d5aceb7dfb71f61d1a` |

**Answer to root's interface question:** the turn-001 `SupplierExact` is met by the canonical
supplier *unchanged*. No new Targets module was needed for the interface. The extra canonical
payment is `signCode r (encodeSyntax (cleanup s))`, inside `staticCode`, inside `rowBound`, for all
three order tests (`signedSign` in the proof module).

## Failed routes (turn 002)

None. No gate failed this turn.

## 2026-11-22T21:57Z — read `opusB/S4-SURVEY.md` (it appeared after my own check)

Two points in it bear on my modules; I agree with both and have not acted on either:

1. **`properClauses` in `StageCallbackSupplier.packets`.** `Emits` is a literal list equation, so a raw
   `high` has to reproduce the proper-clause filter, and the operand half (`ProperField` on ordinal
   notations) has no code-level decider. Dropping the filter from `packets` is *not* free for the
   canonical supplier: canonical grouping discards zero-weight and cancelled occurrences, so a row
   with an improper operand of total weight zero would get packets that can hold although the
   literal row has no value. The filter (or an equivalent raw properness test) is therefore the
   availability check for discarded occurrences, and S4 needs the raw decider. `opusB/` now has a
   `RAW-PROPER-CLAUSE-SOURCE-MAP.md`, so this seems to be in hand there; I have not read it.
2. **Everything after the supplier is typed-computable and order-free**, with code-level programs
   only for the projection kernel, the charts, ranking, names and the stage bound. Consistent with my
   own minimal check above.

## State and next (end of turn 002)

**Gated this turn:** `STAGE-CALLBACK-CANONICAL-ROUTES` and `STAGE-CALLBACK-CANONICAL-SUPPLIER`.
Together with turn 001 this gives, for both controls (any `SelectedWithThreshold f B`):

    Emits canonical B high  ⟹  HighAtStage f B high (stageChildren canonical B)

with `canonical` built only from first-occurrence (`groupTyped`) syntax. Handoff items (a), (b), (c)
are done at the typed level: per-row guards characterise genuine successful reads and the requested
polarity (signed order/equality by the canonical routes, congruence by the accepted packet, ordered
availability by the proper-clause filter plus the paid read ceiling); the join is at one shared
greatest value with one tied table; both callback directions hold at the executable stage bound.

**What is still open — exactly one obligation:** a computable `high` with `Emits alt B high` for a
supplier `alt` that is exact. Nothing gated so far constructs a raw program. Two sub-points:

- *Order.* `canonical` lists a signed row's alternatives in depth-first tree order. A raw program
  built by iterating a level step will produce level order. `SupplierShape`/`SupplierExact` use
  membership only, so the fix is a second supplier `canonicalLevel` whose list is defined by the same
  level iteration the raw program runs, plus one lemma "same members as `routes`"; exactness then
  follows from the gated theorems without redoing any semantics. This should be designed *together
  with* the raw iteration, not before it.
- *Activity test.* The raw iteration must stop at nodes inactive at `top` (finding above), so it is a
  new raw program beside `ActualRawCanonicalZeroPrefixes`, with a raw twin of `CanonicalActive`.

**Ungated drafts:** none.

**Next, in order:**
1. Fix the level-order entry type (accumulated guard codes + raw syntax) and the raw level step from
   `ActualRawCanonicalNode.groupedCode` + a raw activity test + raw guard rendering; freeze
   `canonicalLevel` and prove membership equality with `routes` (typed, small).
2. Raw guard rendering: code-level `compile` on `pairs (labels …)` and `canonicalPacket`, each with a
   calibration equation to `preparedPacketCode`. Not surveyed by either lane yet; this is where the
   remaining unknown is.
3. Raw packet algebra (`append`/`tuplePacket`/`choices`/`prepend`/`cutoffPacket`), `decode`,
   `lowerChart`/`availabilityRows`, assembled with the accepted `eliminatePreparedCode`,
   `clausesCode`, raw charts and `familyCode`. Routine per Opus B's survey; large.
4. Raw properness filter (Opus B).
5. Close: `∃ high, Computable high ∧ HighAtStage f B high (stageChildren alt B)`, then `ForControl`.

Risk to keep in view: `Emits` quantifies over *all* typed families of positive dimension, so every
raw piece must be calibrated on arbitrary encoded input of that form, including clauses the proper
filter rejects and syntax on which `canonicalSuccessor` fails.

---

# Turn 003

## 2026-11-22T22:05Z — STAGE-CALLBACK-LEVEL-ORDER: frozen, then PASS (no failed gate)

- Receipt `1795384974153104577-3150313`: `COMPILE_PASS` `StageCallbackLevelOrderTargets` as first
  written. Frozen:

| file | sha256 |
|---|---|
| `LogicLineages/PermittedControl/StageCallbackLevelOrderTargets.lean` | `e2fca85c61f47dddd205599d1ded35ce92cbe283e6cfa72738316b3fd3f3c8d1` |
| `verification/local-fable-pair-2026-11-22/fable2/STAGE-CALLBACK-LEVEL-ORDER-SOURCE-MAP.md` | `b2893c058a716160fe84a9b720c3b124879c6e0a5cf9c8a03c7ee05e833bb9b0` |

- Receipt `1795385070227028433-3150794`, gate on `StageCallbackLevelOrderStatementChecks`:
  `COMPILE_PASS` `StageCallbackLevelOrderProof` and `…StatementChecks`, first attempt. Seven aliases
  (`fixed_exactLevelOrderRoutes`, `fixed_exactLevelOrderMembers`,
  `fixed_exactSupplierMemberTransfer`, `fixed_exactLevelOrderSupplierShape`,
  `fixed_exactLevelOrderSupplierExact`, `fixed_exactLevelOrderStageCallback`,
  `fixed_fullStageCallbackLevelOrder`), each `[propext, Classical.choice, Quot.sound]`.

| file | sha256 |
|---|---|
| `LogicLineages/PermittedControl/StageCallbackLevelOrderProof.lean` | `f83735cfbe8c82196f9d9ce07f799a986610636250eeb15aadcec9ba83996df4` |
| `LogicLineages/PermittedControl/StageCallbackLevelOrderStatementChecks.lean` | `62eff49c4af4b2711d39a77ee9fab889249c9b7872ada2114f567ccba2a962dc` |

`levelOrder` is the one supplier the close step should talk about:
`Emits levelOrder B high → HighAtStage f B high (stageChildren levelOrder B)` is
`fixed_exactLevelOrderStageCallback`. `canonical` (#1395) is now only the semantic source.

## 2026-11-22T22:08Z — rendering survey, and the raw statements I aim at (written before freezing)

**Packet code.** I use Opus B's frozen `RawPacketAlgebra.encodePacket p = preparedPacketCode p.1 p.2`
and its `appendCode` (`RawPacketAlgebraJoinTargets`, sha `4c8ee91c…04db`, read 22:07Z). No second
encoding. My raw modules import that Targets file only, never its proofs.

**What exists already at code level (all with literal calibrations and `Primrec`):**

| typed | raw | accepted statement |
|---|---|---|
| `CanonicalActive top ts` | `tapeHighestCode top (groupRaw …)` | `ExactRawCanonicalNodeCalibration` (+ `activeTest` ↔ the Prop, to be restated; its accepted proof is private) |
| `tapes (groupTyped ts)` | `candidateTapes (groupRaw …)` | `ExactCanonicalAnswerPairs` |
| `maximalCoefficient (groupTyped ts) a`, `canonicalSuccessor c ts a` | `groupedCode (c, groupRaw …, tape)` | `ExactRawCanonicalNode` + `ExactRawNodeBranches` |
| `labels (groupTyped ts)` | `labelsCode (groupRaw …)` | `ExactRawCanonicalNodeCalibration` |
| `cleanup`, `syntaxBudget` | `cleanupCode`, `syntaxBudgetCode` | `cleanupCalibration`, `BudgetCodeExact` |
| `append` | `RawPacketAlgebra.appendCode` | `ExactAppendCode` (Opus B, frozen; proof on disk, not yet seen gated) |

So the level step itself needs nothing new except assembly. **Three rendering programs do not
exist** and are the whole of the remaining unknown:

- **R1 `guardCode`** for `ActualFiniteFullValueGuards.compile top (pairs ls) a`. Aim:

      guardCode top (ls.map encodeLabel) (a.map Answer.code) = encodePacket (compile top (pairs ls) a)

  for every label list and every tape (including wrong lengths, where `compile` is `([],⊥)`), with
  `Primrec`. Ingredients found: per pair, `lowerPacket` is two operand codes and one of three fixed
  formulas; `topPacket` is `orientedPacket`, whose `strictPacket` case has the accepted code
  `HighFieldPreparedPacket.compile` for `basePacket` (`StableSortedHighField.BasePacketExact`,
  `PostprocessEffective`) plus an appended coordinate slot and `orderGuard`; `choosePolarity` is
  `p ↦ 6p+3`; pair packets are joined by `appendCode`. **Not found:** a code-level form of
  `equalPacket`'s `sameForm (normalizeShortField F) (normalizeShortField G)` (the equal-rank case),
  and a standalone `Primrec` statement for `HighFieldPreparedPacket.compile` (only `postprocess` is
  stated primitive recursive; `highRawComparisonForm` must be checked). These two are where R1 can
  still surprise.
- **R2 `linearCode`** for `canonicalPacket`. Aim:

      linearCode top (encodeSyntax s) (orderCode test) positive
        = encodePacket (canonicalPacket top s.constant s.terms test.test positive)

  It is `groupRaw`, a rank filter for the table, and one row `(c, (slope, x₀) :: names 1 …)` put
  through `testFormula` and `choosePolarity`. Needs the atom/row data encoding
  (`NormalForm.Atom.data`, `Encodable`); nothing accepted renders this row, but nothing in it is deep.
- **R3 `modularCode`** for `ActualGreatestCongruenceRoute.packet`: `prepareCode` (accepted,
  primitive recursive) gives the formula code; the table bytes and `choosePolarity` are to add.

**How it composes into `Emits`.** I state the raw level iteration *parametrically* in a record
`Rendering` of four programs (`append`, `guard`, `linear`, `modular`) with one calibration each
(`Rendering.Exact`). The statement frozen next is

    R.Exact → rowCode R r top (encodeBitRow row) = (levelOrder r top row).map encodePacket

for every row. With `rows.map (alt r top)` in `StageCallbackSupplier.packets` this is exactly the
input of Opus B's join: for a clause `rows`,

    joinCode ((rows.map encodeBitRow).map (rowCode R r top))
      = ((choices (rows.map (levelOrder r top))).map tuplePacket).map encodePacket

by `List.map_map` and `ExactJoinCode`; flat-mapped over `properClausesCode (familyCode (p, raw))`
(#1393, #1311) it is `(packets levelOrder p.1 (top p) (ranked p fs)).map encodePacket`.

**What Opus B's remaining groups must satisfy to plug into the close step** (for root to pass on):

1. Everything on `PreparedPacketCode` through `RawPacketAlgebra.encodePacket`, as it already does.
2. `ExactAppendCode` and `Primrec₂ appendCode` gated — R1 and the leaf join use `appendCode` inside
   my program, so my effectivity proof needs its `Primrec₂`.
3. A residual program `childCode : Nat × Nat × List PreparedPacketCode → RawFamily` (cutoff `C`,
   `top`, the joined packet codes of one chart) with

       childCode (C, top, qs.map encodePacket)
         = encodeFamily (reifyFamily C top (lowerFamily top C (qs.map (prepend top))))

   for **every** `qs : List Packet` — no shape hypothesis, because `Emits` is a bare list equation and
   my side supplies only the list equality above — and `Primrec childCode`.
4. Nothing about charts, ranking or names: `ActualBitFamilyRawCharts.charts`, `familyCode` and
   `ExactRawStageNamesAndCharts` already give those as literal list equalities.

Then `high (C, raw) := (charts raw).map (fun p => childCode (C, top p, (properClausesCode
(familyCode (p, raw))).flatMap (fun rows => joinCode (rows.map (rowCode R p.1 (top p))))))`, and
`Emits levelOrder B high` is a chain of the list equalities above with no semantic step.

## 2026-11-22T22:12Z — STAGE-CALLBACK-RAW-LEVEL: one failed Targets compile, frozen, then PASS

- Receipt `1795385296653086064-3151882`: **FAIL**, first compile of `StageCallbackRawLevelTargets`
  (not yet frozen). Cause: inside `structure Rendering.Exact` the bare names `guard` and `append`
  resolved to the record's own fields. Fix: wrote `StageCallbackCanonicalRoutes.guard` and
  `ActualPreparedSlotAppend.append`. No statement changed in meaning. Failed text kept at
  `drafts/fable2/StageCallbackRawLevelTargets.attempt01-field-name-clash.lean.txt`.
- Receipt `1795385461342556018-3152474`: `COMPILE_PASS` for the Targets module. Frozen:

| file | sha256 |
|---|---|
| `LogicLineages/PermittedControl/StageCallbackRawLevelTargets.lean` | `f0e9a0a09677bebb868ecec8f15148892ddd197ca6937c93a5cda6c16936ee7c` |
| `verification/local-fable-pair-2026-11-22/fable2/STAGE-CALLBACK-RAW-LEVEL-SOURCE-MAP.md` | `8d720d28a03a994d3302a49c8be376eee79e30839e129792ecdf2be87417ca3e` |

- Receipt `1795385515892315614-3152703`, gate on `StageCallbackRawLevelStatementChecks`:
  `COMPILE_PASS` `StageCallbackRawLevelProof` and `…StatementChecks`, first attempt, no warnings.
  Five aliases (`fixed_exactRawActivity`, `fixed_exactRawLevelEntries`,
  `fixed_exactRawSignedPackets`, `fixed_exactRawRowPackets`, `fixed_fullStageCallbackRawLevel`),
  each `[propext, Classical.choice, Quot.sound]`. Evidence: `STAGE-CALLBACK-RAW-LEVEL-EVIDENCE.json`
  (and `STAGE-CALLBACK-LEVEL-ORDER-EVIDENCE.json` for the first key of this turn).

| file | sha256 |
|---|---|
| `LogicLineages/PermittedControl/StageCallbackRawLevelProof.lean` | `923bc6c1ed66fbc6f57ad343743bc221aa68d2803b2f7107bf229e288d79b1f7` |
| `LogicLineages/PermittedControl/StageCallbackRawLevelStatementChecks.lean` | `2f48840c4252544a93f9457fac1e3a2a17b297532052a23003eb31b9633598f0` |

## 2026-11-22T22:14Z — correction to the rendering survey above

Two items I listed as "not found" for R1 do exist; I had not looked in the right modules:

- the equal-rank case: `RawFieldComparisonFormTargets.rawSameForm` with `Primrec₂` and
  `rawSameForm (longFieldCode F) (longFieldCode G) = sameForm F G`. `equalPacket` applies `sameForm`
  to `normalizeShortField F`, so a raw `normalizeShortField` on field codes is still needed;
  `highRawComparisonForm` already uses one internally (`P'`, `Q'`), not yet read.
- effectivity of the base packet compiler: `HighFieldPreparedActualTargets.FullCompilerEffective :
  Primrec compile`.

So R1 has no missing ingredient that I know of; what remains is assembly and the encodings of the
fixed formulas. R2 and R3 are unchanged.

## Failed routes (turn 003)

None mathematical. One failed compile of a not-yet-frozen Targets file (name resolution), above.

## State and next (end of turn 003)

**Gated this turn:** `STAGE-CALLBACK-LEVEL-ORDER` and `STAGE-CALLBACK-RAW-LEVEL`.

**Where the close step stands.** Two list equations bracket what is left:

    Emits levelOrder B high → HighAtStage f B high (stageChildren levelOrder B)      (LEVEL-ORDER)
    R.Exact → rowCode R r top (encodeBitRow row) = (levelOrder r top row).map encodePacket   (RAW-LEVEL)

Between them and a closed statement stand four things, none of them semantic:

1. **Three rendering programs with `Rendering.Exact`** — mine. R1 `guard` (comparison guard on a
   label list), R2 `linear` (canonical linear exit), R3 `modular` (congruence packet). Exact target
   statements are written above under "the raw statements I aim at". The `append` field is Opus B's
   `appendCode` with its `ExactAppendCode`.
2. **Effectivity of `rowCode R`** given primitive recursive components — mine. Not frozen. The level
   iteration is the same shape as the accepted `ActualRawCanonicalZeroPrefixes.level`, whose
   `Primrec₂` proof (`…PrimitiveProof`, `iteratePrimitive`) is the model.
3. **Opus B's residual program** (`childCode`, item 3 of the list above) and its gated
   `ExactAppendCode`/`Primrec₂ appendCode`.
4. **The assembly**: define `high` as written above and prove `Emits levelOrder B high` and
   `Computable high`; then `ForControl` with #1372.

**Ungated drafts:** none.

**Next, in order:** R2 (smallest, fixes the row/atom encoding I also need for R1's fixed formulas),
then R1, then R3, each as its own frozen target `guardCode … = encodePacket …` with `Primrec`; then
item 2; then item 4 once Opus B's item 3 is gated. If root wants to split work: R3 and item 2 are
independent of R1/R2 and of each other.

**Risks.** (i) `Rendering.Exact.guard` quantifies over *all* label lists and tapes, including tapes of
the wrong length; `compile` returns `([],⊥)` there and the raw program must too. (ii) R1's top-rank
pairs go through `orientedPacket`'s three cases with `HighFieldPreparedPacket.compile`, which returns
table *bytes*; appending the coordinate slot means decoding and re-encoding bytes, so the calibration
needs `Encodable.encodek` on `List LowerOperandCode` — routine, but it is the fiddliest step I can
see. (iii) Nothing here has been checked for primitive recursiveness yet; a rendering definition that
is correct but awkward for `Primrec` (nested matches on decoded data) would cost a rewrite, so the
`Primrec` proof should be written alongside each rendering program, not after.

---

# Turn 004

## 2026-11-22T22:16Z — read `opusB/LEDGER.md` first

Gated there, by its own receipts: group 1 join (`RawPacketAlgebraJoinProof`,
`fullRawPacketAlgebraJoin`: `ExactAppendCode`, `Primrec₂ appendCode`, tuple/choices/join) and group 2
guards (`fullRawPacketAlgebraGuard`: prepend, cutoff, bounded, project). Group 3 (residual) has
frozen targets and proof files on disk; I did not see a passing receipt for it in the ledger at that
time. Root's #1396 (`ClosedBlockDecision…`) noted: the close step must end in
`ComputableEmitter f B` with `alt := levelOrder`.

I use Opus B's names `encodePacket` and (next turn) `appendCode`/`appendCodeEq`/`appendPrimitive`
as they are. This turn's two keys need neither `appendCode` nor group 3.

## 2026-11-22T22:19Z — STAGE-CALLBACK-RENDER-LINEAR: frozen, then PASS (no failed gate)

- Receipt `1795385775259559477-3153884`: `COMPILE_PASS` `StageCallbackRenderLinearTargets` as first
  written. Frozen:

| file | sha256 |
|---|---|
| `LogicLineages/PermittedControl/StageCallbackRenderLinearTargets.lean` | `b97ba766d73e097b0ad75a903e0c559f2fb65f2d7cc456092bb37545b0ac1faf` |
| `verification/local-fable-pair-2026-11-22/fable2/STAGE-CALLBACK-RENDER-LINEAR-SOURCE-MAP.md` | `2533ab2d267aed7d1fa3dc09535e24e8d00ad79d6a3475ccdbdfb32f4fb876e5` |

- Receipt `1795385934888220158-3154513`: `COMPILE_PASS` `…LinearCalibrationProof`, first attempt
  (two linter warnings, unused simp argument).
- Receipt `1795385975542327937-3154727`, gate on `StageCallbackRenderLinearStatementChecks`:
  `COMPILE_PASS` `…LinearEffectivityProof` (first attempt) and `…StatementChecks`. Three aliases
  (`fixed_exactLinearCode`, `fixed_linearCodeEffectivity`, `fixed_fullStageCallbackRenderLinear`),
  each `[propext, Classical.choice, Quot.sound]`. Evidence: `STAGE-CALLBACK-RENDER-LINEAR-EVIDENCE.json`.

| file | sha256 |
|---|---|
| `LogicLineages/PermittedControl/StageCallbackRenderLinearCalibrationProof.lean` | `bcf46c253dc26eef9dc86c7b7ae88b40eca8c7e1ec7e6de42c0e69b92a2d6899` |
| `LogicLineages/PermittedControl/StageCallbackRenderLinearEffectivityProof.lean` | `6165406feb14f1d2e985e8f091dd9cc80115549a0dace6e83c24c50be61cb6fc` |
| `LogicLineages/PermittedControl/StageCallbackRenderLinearStatementChecks.lean` | `00a1a07c892b9b97c4ef7cbf71a450f8269a016c0fcfad183f24ce9b4c2a112b` |

`fixed_exactLinearCode` is word for word the `linear` field of `Rendering.Exact` with
`R.linear := linearCode`.

## 2026-11-22T22:24Z — STAGE-CALLBACK-RENDER-MODULAR: frozen, one failed gate, then PASS

- Receipt `1795386052089463613-3155229`: `COMPILE_PASS` `StageCallbackRenderModularTargets` as first
  written. Frozen:

| file | sha256 |
|---|---|
| `LogicLineages/PermittedControl/StageCallbackRenderModularTargets.lean` | `8a23a1717de6cef3466b73bbe9e90ae18f6ebb196cdb7864fdd4f327442c2eef` |
| `verification/local-fable-pair-2026-11-22/fable2/STAGE-CALLBACK-RENDER-MODULAR-SOURCE-MAP.md` | `8127d3cefe7ce32a2e2f43e8e60c43e8109de35ee9e59480ad141a1e43929eef` |

- Receipt `1795386142358861068-3155645`: `…ModularCalibrationProof` `COMPILE_PASS` (first attempt);
  `…ModularEffectivityProof` **FAILED** — deterministic timeout at `whnf` (200000 heartbeats) in the
  final composite `modularPrimitive`. Diagnosis: one long proof whose intermediate `have` types
  mention `formulaCode`, `namedSlots` and `lowerRanksCode` unfolded freely, so a unification that did
  not match at first sight could unfold a fold over `choices`. The component facts
  (`lowerRanksPrimitive`, `formulaStepPrimitive`, `formulaPrimitive`) had elaborated. Fix: split the
  composite into `coordinatePrimitive`, `polarityPrimitive`, `tableBytesPrimitive`,
  `layoutFormulaPrimitive` and a short `modularPrimitive`, and mark `lowerRanksCode`, `formulaCode`,
  `namedSlots`, `coordinateCode`, `polarityCode` `local irreducible` before the composites. No
  heartbeat limit raised, no statement changed. Failed text kept at
  `drafts/fable2/StageCallbackRenderModularEffectivityProof.attempt01-whnf-timeout.lean.txt`.
- Receipt `1795386238420603404-3156069`, gate on `StageCallbackRenderModularStatementChecks`:
  `COMPILE_PASS` `…ModularEffectivityProof` and `…StatementChecks`. Three aliases
  (`fixed_exactModularCode`, `fixed_modularCodeEffectivity`,
  `fixed_fullStageCallbackRenderModular`), each `[propext, Classical.choice, Quot.sound]`.
  Evidence: `STAGE-CALLBACK-RENDER-MODULAR-EVIDENCE.json`.

| file | sha256 |
|---|---|
| `LogicLineages/PermittedControl/StageCallbackRenderModularCalibrationProof.lean` | `d6640e5f4c2d66b927eb5006a1adb47851262a60b8dbf3b6616d84122bb5718a` |
| `LogicLineages/PermittedControl/StageCallbackRenderModularEffectivityProof.lean` | `4b42ee6e31441a2a7b5e64639843939d303db7c747dda38b6addcdaaaeb66658` |
| `LogicLineages/PermittedControl/StageCallbackRenderModularStatementChecks.lean` | `ab72fa14af2a2f2ba6de1a28b0cf9d322cca0b1dfc06fd62893fe0190d4d2c13` |

Point worth knowing: the accepted `SharedRankResidueRow.CodeExact` calibrates the formula code only
through `prepareCode`, which is `none` at modulus zero, while `Rendering.Exact.modular` (and
`Emits`) range over every row. The literal equation and `Primrec` of `formulaCode` hold for every
modulus by the accepted *private* proofs, which I restated (`formulaExact`, `formulaPrimitive`).

## Failed routes (turn 004)

None mathematical. One elaboration timeout, diagnosed and fixed as above.

## State and next (end of turn 004)

**Gated this turn:** `STAGE-CALLBACK-RENDER-LINEAR` and `STAGE-CALLBACK-RENDER-MODULAR`.

**`Rendering.Exact` status, field by field:**

| field | program | calibration | `Primrec` |
|---|---|---|---|
| `append` | `RawPacketAlgebra.appendCode` (Opus B) | `appendCodeEq` — gated by Opus B | `appendPrimitive` — gated by Opus B |
| `linear` | `StageCallbackRender.linearCode` | `fixed_exactLinearCode` — gated | `fixed_linearCodeEffectivity` — gated |
| `modular` | `StageCallbackRender.modularCode` | `fixed_exactModularCode` — gated | `fixed_modularCodeEffectivity` — gated |
| `guard` | **not written** | — | — |

So `Rendering.Exact` is **not yet discharged for any concrete `R`**: the comparison-guard rendering
(R1) is the one missing field. Nothing was started on it this turn beyond the turn-003 survey.

**Still open before `ComputableEmitter f B`** (root's #1396 fixes this as the end point, with
`alt := levelOrder`):

1. R1 `guardCode` with calibration and `Primrec` (mine). Plan, from the survey: per pair,
   `lowerPacket` (two operand codes, one of three fixed formula codes) or `topPacket` =
   `orientedPacket` (`strictPacket` via `HighFieldPreparedPacket.compile` + decode/append one
   coordinate slot + `orderGuard`; `equalPacket` via `rawSameForm` on raw-normalized field codes);
   pairs joined by `appendCode`; `pairs` on label codes by `flatMap`; wrong tape lengths give
   `([],⊥)`. Write each piece with its `Primrec` proof at once, in small lemmas with the heavy
   definitions `local irreducible` (the lesson of this turn's timeout).
2. Assemble `R₀ := ⟨appendCode, guardCode, linearCode, modularCode⟩` and prove `R₀.Exact`.
3. `Primrec` (or `Computable`) of `rowCode R₀` — the level iteration; model:
   `ActualRawCanonicalZeroPrefixesPrimitiveProof`.
4. Opus B's residual `childCode` gated, with the every-packet-list equation.
5. Define `high`, prove `Emits levelOrder B high` and `Computable high`, conclude
   `ComputableEmitter f B` for every `SelectedWithThreshold f B`. Root's reduction then gives
   `ClosedBlockDecision`.

**Ungated drafts:** none.

**Next, in order:** 1, 2, 3 (mine); 5 after 4. Item 3 does not depend on item 1 — it can be stated
for an arbitrary `R` with primitive recursive fields — so it can be done first or in parallel.

**Risk.** R1's `strictPacket` case composes an accepted compiler that returns table *bytes* with a
list append; its calibration needs `tableOf (preparedTableBytes t) = t.map LowerOperand.code`, which
Opus B has (`RawPacketAlgebra.tableBytes`). The `Primrec` side of `HighFieldPreparedPacket.compile`
is `HighFieldPreparedActual.FullCompilerEffective`; I have not yet read its proof module name.

*(Ledger housekeeping, 22:26Z: earlier turns were appended by inserting before the last paragraph of
the file, which left turn 003's closing "Risks" paragraph stranded after turn 004. I moved that
paragraph, unchanged, back to the end of turn 003. No other earlier text was altered.)*

## F01 — measured paired step

**Targets (frozen before the first gate):**
`LogicLineages/PersistentMarking/NumberedWindowInternalCoverCombinedRestrictedMeasuredPairedTargets.lean`
sha256 `2a7b3944c8d0e2341a0844157f98425c37ad8054978010cd498d8861ffe05b71`.
One statement, `ExactOpenCoverCombinedRestrictedMeasuredPairedEdge`: on the actual combined programs,
with `Xm = guardedExchange P.cover s (thinPairedExchange (measuredExchange (selectedMeasure P.R)
(directedX base P.V)))`, the two type-guard conjunctions, `windowAt W ctx dom arg` and ONE accepted
function-level edge `edgeGraph Xm W ctx (rawCons dom cod) f g` give
`edgeGraph Xm W ctx cod (auxiliaryTerm dom cod f arg) (auxiliaryTerm dom cod g arg)` as a plain
derivation. The reverse function edge and the common function measure are not inputs (both are
recovered from the one measured paired edge).

**Second targets (frozen after the first pair passed, before its own first gate):**
`LogicLineages/PersistentMarking/NumberedWindowInternalCoverCombinedRestrictedMeasuredPairedCommonLeastTargets.lean`
sha256 `afd6764568a674c792e84a0539f403896d89aa0573290f0bb370de640f7e1426`.
One statement, `ExactOpenCoverCombinedRestrictedMeasuredPairedCommonLeast`: same four hypotheses, and
a continuation receiving one `x` with `leastGraph P.cover Xm W s ctx cod a x` and
`leastGraph P.cover Xm W s ctx cod b x` (relabelled); conclusion the arbitrary `goal`.

**Receipts (both first-attempt passes; no failed gate this turn):**

| statement | proof module (sha256) | theorem | receipt |
|---|---|---|---|
| `…MeasuredPairedEdge` | `…MeasuredPairedProof.lean` (`8382ea11c02d4aec49bb8432833c734a4c9c4e188b15ddc5aa0847234673951d`) | `exact_OpenCoverCombinedRestrictedMeasuredPairedEdge` | `build-reports/1795387172641849865-3159773.json` |
| `…MeasuredPairedCommonLeast` | `…MeasuredPairedCommonLeastProof.lean` (`b3273261a2d97f5040e97ad1a77e08e75fd9030394c4b27ab966ecff6e633295`) | `exact_OpenCoverCombinedRestrictedMeasuredPairedCommonLeast` | `build-reports/1795387310118722126-3160624.json` |

`#print axioms` for every public theorem in both proof modules: `propext`, `Classical.choice`,
`Quot.sound`. No `sorry`, `axiom` or `native_decide` written.

**Failures:** none. No supplier turned out to be non-generic in the exchange. Step 2 (#1370) is
only ever used at the unmeasured `directedX`, because step 1 strips the measure comparison off the
function-level edge first; step 5 (`guardedOfActualPair`) is generic in `D` and was instantiated at
`measuredExchange N D`.

**Route as built (differs slightly from the prompt's five steps):** instead of calling #1370 and the
common-cover lemma directly, the proof calls accepted `…PairedAux`, which already packages both and
hands back the common cover option plus the unmeasured application edge; a new generic lemma
`measuredUpgrade` then turns (unmeasured guarded paired edge + common cover option + common measure)
into the measured guarded paired edge. The common function measure comes from `compareCases` on the
unpacked function-level edge, the common application measure from `…PairedSharedMeasureParent`.

**Helpers duplicated, not edited:** `edgeRename`, `Moved`/`move`, `shareLeast` are private upstream
and are re-derived as private copies in the new proof modules.

**State:** both statements gated; evidence in `fable2/MEASURED-PAIRED-EVIDENCE.json`, claims in
`fable2/MEASURED-PAIRED-SOURCE-MAP.md`. Nothing ungated is left on disk from this turn.

**Next (not attempted, by instruction):** the premise-free round theorem. What it now has over `Xm`:
`exact_MeasuredExchangePreservesMeasure` (measure preservation), the application edge step and the
common least step here. What it still needs is the measured analogue of
`ExactCombinedApplicationLeastStep` in the "move the held least from `w` to `k`" form — it should
follow from `measuredEdgeOfFunctionMeasure` in both directions plus the same `shareLeast` argument,
since that step takes a held `leastGraph` rather than producing one — and then
`exact_RoundApplicationLeastAt` instantiated at `edge4 Xm W`. I have not checked that last theorem's
hypotheses, so that is a guess about the route, not a finding.

## F02 — measured round

**Targets (hash recorded before the proof module was drafted):**
`LogicLineages/PersistentMarking/NumberedWindowInternalCoverCombinedRestrictedMeasuredRoundTargets.lean`
sha256 `aea17d987c814f1e8c06cea11ee7399604c68603e5786e7043ac62708d3231a1`.
Three statements, each the hypothesis layout of the corresponding `ExactMeasuredCombined…` definition
in `…RoundApplicationRepresentativeTargets.lean` with the application-level exchange `X` replaced by
`Xm` (the unused `let X` is dropped; `let D` and `let Xm` are kept):
`ExactFullyMeasuredApplicationEdgeStepAt`, `ExactFullyMeasuredRoundApplicationLeast`,
`ExactFullyMeasuredLeastRepresentativeApplication`.

**Receipts (both first-attempt passes; no failed gate):**

- `build-reports/1795387537346427977-3161633.json` — `COMPILE_PASS` `…MeasuredRoundTargets` as first
  written (gated after the hash above was recorded, before the proof module existed).
- `build-reports/1795387581939296076-3161890.json` — `COMPILE_PASS` `…MeasuredRoundProof`
  (sha256 `23c9439807b6c84c49dfc52bf16c837aa7dcde1aa64f0ccd72895a9a95db0101`). Theorems
  `exact_FullyMeasuredApplicationEdgeStepAt`, `exact_FullyMeasuredRoundApplicationLeast`,
  `exact_FullyMeasuredLeastRepresentativeApplication`, each `[propext, Classical.choice, Quot.sound]`.
  One linter suggestion (merge two consecutive `intro` lines), no other diagnostics. Targets hash
  re-checked after the gate: unchanged.

**Failures:** none. The motive and the relative premise are generic in the application exchange, so
instantiating at `Xm` met no obstruction.

**How the edge step goes.** The measure of `k` is `exact_MeasuredExchangePreservesMeasure` on the
edge, as in the existing step. For the least: `acceptEdge (edge4 Xm W) …` and `edgeGraph Xm W …` are
the same formula by definition, so the edge feeds F01's
`exact_OpenCoverCombinedRestrictedMeasuredPairedCommonLeast`, which hands back one `x` that is the
`Xm` least at both applications; `valueUnique` on `packedLeastProgram` against the held least gives
`suc x = suc m`, and `outputTransport` rewrites the least at `k`'s application to `m`. The round and
representative theorems are the existing proofs with `X` replaced by `Xm`. The guess at the end of
F01 (a separate "move the held least" lemma from `measuredEdgeOfFunctionMeasure` + `shareLeast`) was
not needed. No private helper had to be copied this time.

**State:** all three statements gated. Evidence `fable2/MEASURED-ROUND-EVIDENCE.json`, claims
`fable2/MEASURED-ROUND-SOURCE-MAP.md`. No ungated draft on disk; no existing `.lean` file edited.

**Next (not attempted):** nothing further was asked. What the three statements still take as input
is the seed application's `Xm` least `m` (and, for the representative, the function's `Xm` least
`x`); producing those is a separate obligation.
