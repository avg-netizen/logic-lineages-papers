# Opus B ledger — join regression + S4 survey (append-only)

All paths relative to `formalization/`. Times UTC.

## Module-name substring

`JoinRegression` — `ls LogicLineages/PermittedControl | grep -i joinregression` was empty on
2026-11-22 before any file was written.

## 2026-11-22T21:34Z — JOIN-REGRESSION targets frozen

- `LogicLineages/PermittedControl/ActualSignedRouteJoinRegressionTargets.lean`
  sha256 `3f3c97f6a484f008062cb56b39e29fff459eb649100793a3c24724f0e6a1dbc9`
- gated alone first: receipt `1795383274001853139-3139721`, COMPILE_PASS.
- source map: `verification/local-fable-pair-2026-11-22/opusB/JOIN-REGRESSION-SOURCE-MAP.md`

## 2026-11-22T21:40Z — JOIN-REGRESSION proof PASS

- `LogicLineages/PermittedControl/ActualSignedRouteJoinRegressionProof.lean`
  sha256 `ed118f1ad4e19aa5a321d397e1c2a238de927f3056a599ad6a58780ce4a87e3e`
- gate receipt `1795383497904313310-3141177`: COMPILE_PASS (Targets verified-cache-hit at the frozen
  hash). Peak RSS 965 MiB. Axioms of `joinRegression` and `fullActualSignedRouteJoinRegression`:
  `[propext, Classical.choice, Quot.sound]`.
- First attempt passed; no failed routes. Log has 10 linter warnings (unused fallback branches of two
  `first | …` combinators in the private lemma `singletonFamilyLength`), no errors.
- Outcome: the regression is TRUE. `project C (tuplePacket [pinned ops₁ C, pinned ops₂ (C+1)])` and
  the `prepend`ed version are unsatisfiable for every `f`, `ρ`, `top`, `C` and every pair of tables,
  while each row projected alone is satisfiable; the joined packet is emitted by `lowerFamily` as
  exactly one residual, and that residual's `LowerMatrix` is false.
- Evidence: `verification/local-fable-pair-2026-11-22/opusB/JOIN-REGRESSION-EVIDENCE.json`.

## 2026-11-22T21:50Z — S4 survey computability probe (not a target, not for a record)

- `LogicLineages/PermittedControl/JoinRegressionLaneS4ComputabilityProbe.lean` — unmarked copies of
  `ActualGreatestRouteResidual.decodeRoute` / `lowerFamily` with `rfl` equations to the originals,
  and a typed composite `childFromRows` = `encodeFamily ∘ reifyFamily ∘ lowerFamily ∘ map prepend ∘
  flatMap (choices ↦ tuplePacket)`.
- v1 receipt `1795383761091120902-3144979` FAILED only on the `rfl` equations (defs not `@[expose]`d);
  kept as `drafts/opusB/JoinRegressionLaneS4ComputabilityProbe.v1.lean` with a note.
- v2 (added `@[expose]`) receipt `1795383773241033889-3145032` COMPILE_PASS: the code generator
  accepts both bodies, so their `noncomputable` markers are not forced. This is Lean-level
  compilability only, not Mathlib `Computable` on raw codes.

## 2026-11-22T22:00Z — S4 survey written

- `verification/local-fable-pair-2026-11-22/opusB/S4-SURVEY.md` (reading plus the one probe above).

## State and next

- JOIN-REGRESSION: proved and gated (receipt `1795383497904313310-3141177`); the regression is TRUE
  (no defect in the join/projection order). Evidence JSON written. Nothing drafted is left ungated.
- Probe module `JoinRegressionLaneS4ComputabilityProbe.lean` is survey evidence only, not proposed for a
  record; root may archive it.
- Next, for whoever takes S4: decide whether `properClauses` stays in `StageCallbackSupplier.packets`
  (then a code-level `ProperField` decider is owed) or is dropped (then `SupplierExact` must cover
  non-admitted rows). After that come code-level `append`/`tuplePacket`/`prepend`/`decode`/`reify`
  programs with calibration lemmas through `preparedPacketCode`/`encodeFamily`, reusing
  `eliminatePreparedCode` (#728), `clausesCode` (#1343) and `LinearRows.Code.atoms`.

## 2026-11-22T21:54Z — Task 3 RAW-PROPER-CLAUSE targets frozen

- Root moved the probe to `opusB/probes/JoinRegressionLaneS4ComputabilityProbe.lean.txt` (noted).
- Prefix `RawProperClause`: no existing file in `LogicLineages/PermittedControl/` before mine.
- `LogicLineages/PermittedControl/RawProperClauseTargets.lean`
  sha256 `5b99f183d434d93ad0a14506fb10a550e319b14dec06338bf2160502476b9aab`;
  gated alone: receipt `1795384447638511844-3147665`, COMPILE_PASS.
- Source map: `opusB/RAW-PROPER-CLAUSE-SOURCE-MAP.md`.
- Reused (not rewritten): `OrdinalComparison.rawComparisonCode` + `rawComparisonOrdinalCorrect` +
  `rawComparisonPrimitiveRecursive`; `OrdinalComparison.encodedOrdinalFiniteRemainder` +
  `OrdinalSuccessorProgram.classification` + `primitive`; `rawNoteDecodeEncode`;
  `ActualBitFamilyRawClosed.admittedCode` (#1334). No second encoding.

## 2026-11-22T22:00Z — RAW-PROPER-CLAUSE proof PASS

- `LogicLineages/PermittedControl/RawProperClauseProof.lean`
  sha256 `227609671226715f525e39cd89745c85dfc585294b61bdb1d91faa50906b77fb`.
- Gate receipt `1795384636944616848-3148397`: COMPILE_PASS on the first attempt (Targets
  verified-cache-hit at the frozen hash). Peak RSS 963 MiB. Axioms of `exactRawProperClauses` and
  `fullRawProperClause`: `[propext, Classical.choice, Quot.sound]`.
- The same gate compiled the existing, unchanged, uncached `ActualBitFamilyRawClosedPrimitiveProof`
  (#1334), which my proof imports for `exactClosedRawEffectivity`.
- 6 linter warnings: unused `first` fallbacks. No errors.
- Evidence: `opusB/RAW-PROPER-CLAUSE-EVIDENCE.json`.
- Encoding facts for the emission program:
  (i) `LowerOperand.code` is injective (`exactOperandCodeInjective`, via `rawNoteDecodeEncode`), so the
  codes carry the full notation and the filter needs no extra data.
  (ii) The deciders are calibrated only on encoder images. On arbitrary naturals (non-NF raw notation
  codes, field tags ≥ 2) they return some Boolean with no claim. `Emits` only meets `encodeFamily fs`,
  so that suffices.
  (iii) The filter keeps the clause order (`filter`), so `properClausesCode (encodeFamily fs)` is
  literally `encodeFamily (properClauses fs)`.
- The filter does not need to be dropped, so `PROPER-CLAUSES-NOTE.md` was not written.

## State and next (updated)

All three tasks are gated. Nothing is drafted and ungated. For S4, the raw `high` can start with
`properClausesCode` (Primrec) in place of `properClauses`. Still owed downstream are the code-level
`choices`/`tuplePacket`/`prepend`/`decode`/`reify` programs (see `S4-SURVEY.md`).

## 2026-11-22T22:03Z — Task 4 RAW-PACKET-ALGEBRA group 1 (join) targets frozen

- Prefix `RawPacketAlgebra`: unused before (count 0).
- `LogicLineages/PermittedControl/RawPacketAlgebraJoinTargets.lean` sha256 `4c8ee91c67c2648f74cb2dc06ace5b610f859a01654122f0fa3098cef2fb04db`; gated alone: receipt
  `1795384978040632556-3150351` COMPILE_PASS. Source map `opusB/RAW-PACKET-ALGEBRA-JOIN-SOURCE-MAP.md`.

## 2026-11-22T22:10Z — group 1 (join) PASS

- CalibrationProof v1 FAILED (receipt `1795385018557364166-3150570`): `variable` is a keyword as a case
  alternative. The draft is kept in `drafts/opusB/`. v2 (`«variable»`) passed: receipt `1795385033144432493-3150611`.
- EffectivityProof passed on the first attempt: receipt `1795385090686262557-3150859`.
- Bundle `RawPacketAlgebraJoinProof` passed: receipt `1795385120370042416-3151069` (the other three were
  verified-cache-hit). Axioms standard. Evidence `opusB/RAW-PACKET-ALGEBRA-JOIN-EVIDENCE.json`.

## 2026-11-22T22:06Z — group 2 (guards) targets frozen

- `LogicLineages/PermittedControl/RawPacketAlgebraGuardTargets.lean` sha256
  `6eb200a5609b4e1b8c4ccab3441d9d51cb5afebb8125910d04cd03f7e280f4cc`; receipt `1795385184265797565-3151419`.
  Source map `opusB/RAW-PACKET-ALGEBRA-GUARD-SOURCE-MAP.md`.

## 22:07Z — group 2 (guards) PASS

- GuardProof v1 FAILED (receipt `1795385216544389891-3151620`): its open list named a nonexistent
  `PreparedProjection.LongFieldCode`. The draft is kept. v2 sha256 `ba980cc8f4ce9b65e95a6a0cc1c1ce6e9fb324addd4a4e236a6f2933bc5b3c1f` passed: receipt
  `1795385229420686671-3151708`. Axioms standard. Evidence `opusB/RAW-PACKET-ALGEBRA-GUARD-EVIDENCE.json`.

## 2026-11-22T22:10Z — group 3 (residual) targets frozen

- `LogicLineages/PermittedControl/RawPacketAlgebraResidualTargets.lean` sha256
  `2f88a8c86fa34c3477941cea211b1d967a1b95ef33225eb19f3a01e3947b0bd2`; receipt `1795385442097803207-3152345`.
- NEW minimal composite code `ResidualCode`/`encodeResidual` (a tuple of existing field codes), flagged in
  the source map.

## 22:3xZ — group 3 (residual) PASS

- CalibrationProof v1 and v2 FAILED on whnf heartbeat timeouts (receipts `1795385485583304557-3152570`,
  `1795385543906661322-3152844`). In both, a definitional check unfolded `Encodable.decode`/`encode` of an
  atom payload. Fixed by a `simp only [decodeAtomsCode, List.foldr_cons]` step lemma. Both drafts are kept.
  v3 passed: receipt `1795385656636293085-3153395`.
- EffectivityProof passed: receipt `1795385675400117186-3153490`. Bundle passed: receipt
  `1795385685312832325-3153529`. Evidence `opusB/RAW-PACKET-ALGEBRA-RESIDUAL-EVIDENCE.json`.
- Root relayed Fable-2's interface requests: `appendCode` (done, group 1), and one residual
  program `childCode (C, top, qs.map encodePacket) = encodeFamily (reifyFamily C top (lowerFamily top C (qs.map (prepend top))))`,
  no shape hypothesis, Primrec. This becomes group 5's exact statement.

## 2026-11-22T22:16Z — groups 4 and 5 targets frozen

- `RawPacketAlgebraReifyTargets.lean` sha256 `1520ff85775a6723b2aaed958428655c7207eb4162c05ef9b36946a5d350a92b`.
- `RawPacketAlgebraChildTargets.lean` sha256 `0700af0e8508a7691918c0e81f194fa72302d8b16796b12842f4a0bb54b022ee`.
- Both gated together: receipt `1795385752127892140-3153782`. Source map
  `opusB/RAW-PACKET-ALGEBRA-REIFY-CHILD-SOURCE-MAP.md`.

## 22:4xZ — groups 4 and 5 PASS; Task 4 complete

- ReifyProof passed on the first attempt: receipt `1795385836912543661-3154100`.
- ChildProof failed three times, all on elaboration only (receipts `1795385855593800890-3154180`,
  `1795385869794241763-3154230`, `1795385938591068432-3154541`):
  - v1: missing transitive import;
  - v2, v3: defeq/unification timeouts in the Primrec composition.
  Fixed by elaborating the composition without an expected type. Drafts are kept in `drafts/opusB/`.
  v4 passed: receipt `1795385987212346157-3154936`, which also cache-verified every group 1–4 module.
- `exactChildCode` is Fable-2's interface item 2, literally and with no shape hypothesis. `childEffectivity`
  gives Primrec and Computable.
- Evidence `opusB/RAW-PACKET-ALGEBRA-REIFY-CHILD-EVIDENCE.json`.

## State and next (updated)

- Tasks 1–4 are gated. Nothing is drafted and ungated.
- The one new code is `ResidualCode`/`encodeResidual` (group 3), internal to `childCode`.
- Lean pitfall for later lanes: Primrec compositions whose argument order differs from the target
  must be elaborated without an expected type (`have h := f.comp g; exact h`). Otherwise
  higher-order unification unfolds the decoders and times out.

## 22:5xZ — Task 5 (congruence rendering): STOPPED, Fable-2 already owns it

- `LogicLineages/PermittedControl/StageCallbackRenderModularTargets.lean` exists. It is Fable-2's file,
  mtime 16:20:49 −0600 (22:20Z), sha256 `8a23a1717de6cef3466b73bbe9e90ae18f6ebb196cdb7864fdd4f327442c2eef`.
  It is not yet mentioned in `fable2/LEDGER.md`.
- It defines `StageCallbackRender.modularCode top m s positive` (coordinate-slot table from
  `lowerRanksCode`, `SharedRankResidueRow.formulaCode`, `polarityCode`). Its `ExactModularCode` is literally
  the `modular` clause of `Rendering.Exact`, with the same argument order. `ModularCodeEffectivity` asks for
  `Primrec` of the uncurried `modularCode`.
- No proof module exists for it yet. Per root's instruction I did not duplicate it, and I created no
  `RawCongruenceRendering*` file (prefix unused, count 0).

## 2026-11-22T22:32Z — Task 6 guard rendering: targets frozen

- Prefix `StageCallbackGuardRender` was unused (count 0). No Fable-2 module touched.
- `LogicLineages/PermittedControl/StageCallbackGuardRenderTargets.lean` sha256
  `ad8b4423a3a13e485bf91f28687717210c49773ab3f25de518875ba1e9abe6e3`; receipt `1795386726818073956-3157693`.
  Source map `opusB/STAGE-CALLBACK-GUARD-RENDER-SOURCE-MAP.md`.

## Task 6 progress

- Guard CalibrationProof passed on the first attempt: receipt `1795386836133607408-3158099`. It also compiled
  the existing, unchanged, uncached `HighFieldComparisonStatementChecks` and `RawFieldComparisonFormStatementChecks`.
- Guard EffectivityProof v1 FAILED (receipt `1795386893166228144-3158377`): a stuck Primcodable instance from
  untyped projections. The draft is kept. v2 passed: receipt `1795386918858553059-3158529`.
- Guard StatementChecks passed: receipt `1795386947138244103-3158617`.
- Record Targets `StageCallbackGuardRenderRecordTargets.lean`, sha256
  `36e87ab0249cd8238ee523f5ad84435f1515eac1bcf4f66998c5ac7559af1fa7`, frozen after compiling alone (receipt
  `1795386961593199923-3158797`). It defines `R₀ := ⟨appendCode, guardCode, linearCode, modularCode⟩`,
  `ExactR₀ := Rendering.Exact R₀`, and `EffectiveR₀ := StageEmitter.RenderingEffective R₀` (Opus A's frozen
  hypothesis form).
- Record Proof sha256 `7a84daae0d05faa242b5f9c975b4dbbba7f86c40e316896a4ceb81476ea55214` passed: receipt `1795386972428225726-3158838`. `exactR₀`, `effectiveR₀` and `fullR₀`
  have standard axioms. Evidence: `opusB/STAGE-CALLBACK-GUARD-RENDER-EVIDENCE.json`.

## State and next (end of Task 6)

The `guard` field is `StageCallbackGuardRender.guardCode`, with `StatementChecks.fixed_exactGuardCode` and
`fixed_guardCodeEffectivity.2.2`. `R₀` is gated with `Rendering.Exact R₀` and `StageEmitter.RenderingEffective R₀`.
Nothing is drafted and ungated. The frozen `guard` field is met as stated, with no hypothesis. Wrong-length tapes are
handled by the same recursion as `compile`.

## Close — unconditional `ClosedBlockDecision`

- Root froze Opus A's `StageEmitterGuardTargets` (`GuardExact`, `GuardEffective`, `exactClosedBlockDecisionFromGuard`).
- `StageCallbackGuardRenderCloseProof.lean` sha256 `f39fa010a82d701ceaac1e6b573ec90506fbadc15c7036391f63696af15a84fb`:
  - `guardExact : StageEmitter.GuardExact guardCode`
  - `guardEffective : StageEmitter.GuardEffective guardCode`
  - `closedBlockDecision : ClosedBlockDecision := exactClosedBlockDecisionFromGuard guardCode guardExact guardEffective`
- v1 FAILED (receipt `1795387030515883198-3159090`): a missing public import. The draft is kept. v2 PASSED:
  receipt `1795387043908318394-3159191`. `#print axioms closedBlockDecision` gives `[propext, Classical.choice, Quot.sound]`.
- Evidence JSON updated (`STAGE-CALLBACK-GUARD-RENDER-EVIDENCE.json`). The `R₀` record modules from before
  remain gated and valid but are redundant with `renderingWith`.

## 22:51Z — Task 7 (M4, GroundScalarCircuit) group A targets frozen

- Prefix `GroundScalarCircuit` was unused before. Read `opusA/P17-GROUND-GAP.md`, `P17-THM-ARITHMETIC-CORRESPONDENCE.md`
  and `GROUND-INTERFACE-FOR-M4.md`. The interface appeared while I was drafting; the Targets follow it.
- `LogicLineages/PermittedControl/GroundScalarCircuitTargets.lean` sha256
  `bcd325cc3566354e748cd7c6536e0bb7315b7ad155edc8ef63d3d275bb6917af`; receipt `1795387859861003022-3163107`.
  Source map `opusB/GROUND-SCALAR-CIRCUIT-SOURCE-MAP.md`. Earlier drafts of this same unfrozen file were compiled
  while it was being revised to the interface (receipts `…1795387675551006345…`, `…1795387773254594816…`, `…1795387842088158537…`).

## Task 7 group A PASS

- ShapeProof v1 FAILED (receipt `1795388014775487636-3163682`): a missing `nil_append`, a wrong namespace for
  `ClosedPositive`, and omega blocked by tuple projections. The draft is kept. v2 PASSED: receipt
  `1795388068199463409-3163836`, sha256 `c22ed0b1…2584`. Gives `blockShape : BlockShape`.
- SemanticsProof failed four times on tactic details: `runAppend` match handling, an `unfold` missing in hypotheses, and
  no `Decidable` instance for `Counter` (receipts `1795388135210852679-3164073`, `…179911253951-3164264`,
  `…212043310809-3164427`, `…232521509580-3164481`). Draft v1 is kept. It then PASSED: receipt
  `1795388246572451897-3164572`. Gives `blockCorrect : BlockCorrect` and `fullGroundScalarCircuit`, with standard axioms.

## Task 7 group B targets frozen

- `LogicLineages/PermittedControl/GroundScalarCircuitCodeTargets.lean` sha256
  `2df132edd75e3c5f622f48eea5a050e76c9265ae1ae31ef71e0a4cccba522194`; compiled alone, receipt `1795388388019117185-3165046`.
  An earlier unfrozen draft failed (receipt `1795388368698249801-3164973`) on non-dependent `if`s in the well-founded
  `relCode`. Contents:
  - `renameName`, `renameGate`, `leafGate`, `addGate`, `shiftGate`;
  - `relCode`, the circuit by recursion on `scalarCode`;
  - `strictRowCode`, `weakRowCode`, `counterCode`, `queryCode`;
  - `CircuitCalibration`, the typed↔code literal calibration at every counter;
  - `ExactQueryCode`, verbatim from Opus A's interface;
  - `QueryCodeEffectivity`, Primrec of the uncurried `queryCode`.

## Task 7 group B PASS — M4 complete

- CalibrationProof failed twice on small tactic issues (receipts `1795388490129572369-3165419`,
  `1795388517926159125-3165512`). The draft is kept. It then PASSED: receipt `1795388538647725439-3165561`.
  Gives `circuitCalibration` and `exactQueryCode`.
- EffectivityProof PASSED on the first attempt: receipt `1795388629395778444-3165796`. Gives `relCodePrimitive` and
  `queryCodeEffectivity`.
- StatementChecks PASSED: receipt `1795388649799408449-3165892`. All axioms are standard.
- Evidence: `opusB/GROUND-SCALAR-CIRCUIT-EVIDENCE.json`. Nothing is drafted and ungated.
