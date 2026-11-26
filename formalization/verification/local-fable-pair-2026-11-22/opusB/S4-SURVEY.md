# S4 survey: raw/computable forms for the emission equation (Opus B, 2026-11-22)

This is a reading survey for Fable-2's plan step S4 (`StageCallbackSupplier.Emits`). Paths are relative
to `formalization/LogicLineages/PermittedControl/` unless they say otherwise. "#N" is a record under
`verification/new-paper-set-2026-11-18/accepted/`, matched by the module's `source_pins`.
I wrote "not found" only after grepping the whole `PermittedControl/` tree, and
`OrdinalComparison/` where it says so.

## What has to be computable

`ActualBitFamilyRawDriver.HighProgram := Nat × RawFamily → List RawFamily`. `ForControl` (#1372)
asks for Mathlib `Computable high`. `Emits alt B high` is a literal list equation **for every typed
`fs` of positive dimension**, not only for reachable families:
`high (stageBound B (encodeFamily fs), encodeFamily fs) = (stageChildren alt B fs).map encodeFamily`.
`RawFamily` is plain `Nat`/`Int`/`Bool` data, but typed `Family` holds `LowerOperand`
(`ValueField`, `NONote`), and I found no `Primcodable` instance for `LowerOperand`, `ValueField` or
`NONote` (there is only a non-instance `def rawONotePrimcodable : Primcodable ONote` in
`OrdinalComparison/RawNotationCode.lean:61`). So "computable" here means a **code-level** program
with a calibration equation through the encodings. A typed function that Lean can compile is not
enough on its own.

Lean-level compilability check: a `def` that is not marked `noncomputable` has already been compiled
by Lean, so it compiles. For the two marked residual functions I ran a probe,
`JoinRegressionLaneS4ComputabilityProbe.lean` (receipt `1795383773241033889-3145032`, COMPILE_PASS).
It holds unmarked copies with `rfl` equations to the originals, plus a typed composite
`encodeFamily ∘ reifyFamily ∘ lowerFamily ∘ map prepend ∘ flatMap (choices ↦ tuplePacket)`.

## Table

| function (module · decl) | `noncomputable`? why | raw / code counterpart | legacy order? |
|---|---|---|---|
| `OriginalPrintedLiteralRowBridgeTargets` · `properClauses` (#1257) | **yes, forced**: `family.filter (fun rows => @decide (AdmittedLiteralClause rows) (Classical.propDecidable _))`. `AdmittedLiteralClause` = ∀ row, `row.1.1.Admitted ∧ ∀ t ∈ row.1.2.2, properOperand t.2`. `properOperand` (`MixedSameRankResidueTargets`) reduces to `FieldComparison.ProperField` (`FieldComparisonTargets:32`): `Order.IsSuccLimit lam.1.repr ∧ (mu.1.repr = 0 ∨ Order.IsSuccLimit mu.1.repr) ∧ mu.1.repr < lam.1.repr`, which are predicates on `Ordinal` | **test half only**: `ActualBitFamilyRawClosed.admittedCode : TestCode → Bool` (#1334, `Primrec admittedCode`). I found no standalone calibration `admittedCode (encodeTest t) = decide t.Admitted`, only through `clauseCode`/`closedClause`. **Operand half not found**: there is no code-level `properOperand`/`ProperField` decider in `PermittedControl`. `ActualRawMixedFamilyCeilingTargets:30` says the raw majorant deliberately covers "even the clauses which the typed proper filter rejects", and `ActualBitFamilyRawReadCeilingTargets:48` says "the bound does not test properness itself". A possible ingredient outside PermittedControl is `OrdinalComparison.encodedOrdinalFiniteRemainder` (Primrec; `ActualOrdinalFiniteRemainderClassification`: `= 0 ↔ repr = 0 ∨ IsSuccLimit repr`, `OrdinalSuccessorProgramTargets.lean`). It is listed in the older `verification/local-resume-2026-10-31/ordinal/PROMOTIONS.json`, not under new-paper-set `accepted/`. I found no code-level comparator for `mu.repr < lam.repr` | no |
| `ActualSignedRouteCartesianTargets` · `choices`, `tuplePacket` (#1238) | no (`def`) | not found (no `choicesCode`/`tuplePacketCode`). #877 "ordered-cartesian-fold" (scope: "physical flatMap on the original standard-coded ordered lists") pins no `.lean` file in `source_pins`, so I could not tie it to these declarations | no |
| `ActualPreparedSlotAppendTargets` · `append`, `shift`, `shiftName` (#1166) | no (`def`) | not found. Ingredients: `LinearRows.Code.mapAtoms` (formula-code atom map, `OrdinalComparison/.../LinearRowsCodeDefinitions:29`) and the literal `Formula.encode` tags (`conjunction ↦ 6·pair+4`). Table side: `preparedTableBytes = Encodable.encode (table.map LowerOperand.code)` | no |
| `ActualSymbolicPredecessorProjectionTargets` · `prepend`, `predecessorPacket` (#1285) | no (`def`; `if top = 0` on `Nat`) | not found (it is one literal packet plus `append`) | no |
| `ActualSelectedSignedRouteProjectionTargets` · `project`, `bounded`, `cutoffPacket` (#1227) | no (`def`). `project` = `(q.1, eliminatePreparedFormula q.2)` with `q = append (cutoffPacket minimum) p` | **elimination yes**: `PreparedProjection.eliminatePreparedCode` with `PreparedProjectionCodeExact` (#728): `Primrec eliminatePreparedCode` and `eliminatePreparedCode (preparedPacketCode table p) = preparedPacketCode table (eliminatePreparedFormula p)`. Below that, #728 pins `LinearRowsCodeStatementChecks` (`literal_code_calibration`: `Code.eliminate i p.encode = (eliminate i p).encode`; `actual_numeric_programs`: `Primrec₂ Code.eliminate`). `bounded`/`cutoffPacket` (the `append` of the cutoff row) are not found at code level | no |
| `OriginalProjectedMatrixDecodeTargets` · `decode`, `decodeAtoms`, `decodeTerm` (#1127) | no (`def`) | not found. Ingredients: `LinearRows.Code.atoms` (`Primrec`, `atoms_primitive`, `LinearRowsCodeRecursionProof:162`), `atoms_calibration : Code.atoms p.encode = (atoms p).map (fun a => Encodable.encode a.data)` (`LinearRowsCodeCalibrationProof:70`; proved in the tree, not a frozen target of any record I found), `Code.decodeAtom` | no |
| `ActualGreatestRouteResidualTargets` · `decodeRoute`, `lowerFamily` (#1268) | **marked, but not forced**: the body uses only `project`, `decode`, `Option.map`, `keep` (`List.filter` with `decide (op.rank < top)`). Probe receipt `1795383773241033889-3145032` compiles both unmarked, `rfl`-equal to the originals | not found (`keep`, `decodeRoute`, `lowerFamily`, `Residual` have no code versions) | no |
| `ActualGuardedResidualBitFamilyTargets` · `reify`, `reifyFamily` (#1281) | no (`def`) | **partial**: the `clauses` part has `OriginalPrintedRawClauseAssembly.clausesCode` (#1343): `clausesCode (p.encode, polarity, pre.map encodeRow, tail.map encodeRow) = encodeFamily (clauses pre tail p polarity)`, `Primrec clausesCode`. The prefix `lowerChart C top ++ ·` and `OriginalProjectedMatrixSemantics.availabilityRows` (`ops.map availableRow`) are not found at code level, though both are literal row lists | no |
| `ActualLowerRankChartRowsTargets` · `lowerChart`, `fundRow`, `risingRow` (#1277) | no (`def`; `List.range`) | not found | no |
| chart enumeration: `ActualNamedBitFamilyHighTargets` · `charts` (#1308) | **yes, forced**: `filter (fun p => @decide (0 < p.1 ∧ Consistent p) (Classical.propDecidable _))` | **yes, with literal list equality**: `ActualBitFamilyRawCharts.charts := nonemptyPatterns (names raw)` (#1313, `Primrec charts`), and `ActualRawStageCutoff.ExactRawStageNamesAndCharts` (#1336): `ActualBitFamilyRawCharts.charts (encodeFamily family) = ActualNamedBitFamilyHigh.charts (names (encodeFamily family))` and `Supplied family (names …)` | no (raw `names` is sorted, `namesFrom`/`range`) |
| `ActualBitFamilyHighTargets` · `names` (#1292) | **yes, forced**: `(coordinates family).toList` (`Finset.toList`) | replaced by `ActualBitFamilyRawLayout.names` (#1298, `Primrec names`, sorted, `toFinset` = `coordinates`). Fable-2's `stageChildren` already uses the raw `names` | **yes** (Finset order). Only the old `ActualBitFamilyHigh.charts/cutoff/compile` use it; S1 does not |
| `ActualBitFamilyHighTargets` · `ranked`, `renameBit` (#1292) | no (`def`) | `ActualBitFamilyRawRank.familyCode` (#1311): `familyCode (p, encodeFamily family) = encodeFamily (ranked p family)`, `Primrec familyCode` | no |
| `OriginalPrintedPlainMatrixLinearProjectionTargets` · `top` | no (`branch.1 - 1`) | trivial | no |
| `ActualRawStageCutoffTargets` · `stageBound`, `chartCost` (#1336) | no | already raw: `Primrec₂ stageBound`, and `cutoff ≤ stageBound` (`ExactRawStageCutoffMajorant`) | no |
| `ActualBitFamilyRawLayoutTargets` · `encodeFamily`, `encodeBitRow` (#1298) | no (`def`) | it is the encoder (`encodeRow` = `(encodeTest, const, map encodeWeighted)`, operands through `LowerOperand.code`/`longFieldCode`). `Primrec occurrences`, `Primrec names` | no |
| for contrast, the legacy supplier: `ActualSignedRouteCartesian.rowPackets`, `matrixTuples`; `ActualPaidMixedMatrixTuples.alternatives`, `tuples`; `OriginalRankedLiteralClauseHigh.highPackets` | yes, forced through `ActualBoundedSignedRoutes.routes`/`active`, which use `ActualRankedNormalizationSyntax.normalizedTerms` (`weights.support.toList`, a Finsupp `Finset.toList`), `ActualFiniteSignedNodeBranch.nodePattern`/`nodePacket`/`nodeCoefficient`, and `ActualSymbolicZeroSuccessor.successor`; `highPackets` also uses `properClauses` | none (this is what S3 replaces) | **yes** |

## The three findings that matter most

1. **`properClauses` is the one S4 step that is both forced-noncomputable and without a raw
   counterpart.** The obstruction is not `Test.Admitted` (raw `admittedCode`, #1334). It is
   `ProperField` on ordinal notations: `IsSuccLimit` and `<` of `NONote.repr`. `Emits` is a literal
   equation over all families, and `packets` filters with `properClauses`, so a raw `high` must decide
   properness on `longFieldCode` operand codes. The alternative is for S1 to drop the filter from
   `packets`/`SupplierExact`. `OriginalPrintedLiteralRowBridge.ExactLiteralRowProper` (a row that holds
   is admitted) suggests that is semantically harmless, but `SupplierExact` currently assumes
   `AdmittedOperandRow`. This should be decided before S1 is frozen, if it is not already.
   A possible decider ingredient (`encodedOrdinalFiniteRemainder`) exists only in the older ordinal
   layer. I did not find a code comparator for `<`.
2. **Only one packet-level operation has an accepted code-level program: the projection kernel**
   (`eliminatePreparedCode`, #728, Primrec plus commuting equation). `append`/`shift`/`tuplePacket`/
   `choices`/`prepend`/`cutoffPacket`/`bounded`/`decode`/`keep`/`decodeRoute`/`lowerFamily`/
   `availabilityRows`/`lowerChart` and the `lowerChart`-prefix part of `reify` all have no raw form.
   They are typed-computable, though: `decodeRoute`/`lowerFamily`'s `noncomputable` is unforced (probe
   passed). Ingredients exist: `LinearRows.Code.atoms` + `atoms_calibration`, `Code.mapAtoms`,
   `Code.conjunction`, `clausesCode` (#1343) for the `clauses` core of `reify`, and Mathlib list
   encode/decode for `preparedTableBytes`. So S4 is new but routine code-level work with
   calibration lemmas. The packet type S3 emits should be one whose `(preparedTableBytes, encode)`
   code these programs can produce.
3. **No legacy incidental order in the S4 pipeline after the supplier.** None of `properClauses`,
   `choices`, `tuplePacket`, `prepend`, `project`, `decode`, `lowerFamily`, `reify`, `lowerChart`,
   the raw charts, `ranked` or `stageBound` touches `normalizedTerms`/`nodePattern`/`successor` or a
   `Finset` order. The only Finset-order function nearby is `ActualBitFamilyHigh.names`, which S1
   already avoids. The chart enumeration, ranking, names and stage bound are already raw, with
   *literal* list equalities (#1313, #1336, #1311, #1298), so the chart order of the raw program and
   of `stageChildren` agree by an accepted theorem. The legacy order enters only through a supplier
   built from `routes` (the S2 legacy one). A canonical S3 supplier avoids it by construction.

## Not checked

- `ActualGreatestCongruenceRoute.packet` (S3d) and `ActualFiniteFullValueGuards.compile` (S3a):
  not surveyed beyond noting that the latter is a `def`.
- Whether `Formula.encode`/`LowerOperand.code` are injective, i.e. whether a raw program could
  decode back to typed data instead of working on codes: not checked.
