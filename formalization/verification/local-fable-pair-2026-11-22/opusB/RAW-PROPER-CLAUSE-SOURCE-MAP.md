# RAW-PROPER-CLAUSE — source map (Opus B)

Targets: `LogicLineages/PermittedControl/RawProperClauseTargets.lean`
(namespace `LogicLineages.PermittedControl.RawProperClause`), sha256
`5b99f183d434d93ad0a14506fb10a550e319b14dec06338bf2160502476b9aab`, frozen 2026-11-22T21:54Z after the
Targets module alone compiled (receipt `1795384447638511844-3147665`).

## What it serves

Root's Task 3, from `opusB/S4-SURVEY.md` finding 1. `OriginalPrintedLiteralRowBridge.properClauses`
(#1257) filters with `Classical.propDecidable (AdmittedLiteralClause rows)`. Fable-2's frozen
`StageCallbackSupplier.packets` keeps that filter, and `Emits` is a literal list equation, so a
computable `high` needs a code-level filter whose output on `encodeFamily family` is literally
`encodeFamily (properClauses family)`.

## Encoding used (no new encoding)

Operands go through the existing `PreparedProjection.LowerOperand.code`:
- `coordinate r ↦ (0,r,(0,0,0,0))`;
- `ordinary r F ↦ (1,r,longFieldCode F)`;
- `count r λ μ ↦ (2,r,longFieldCode (.entry 0 λ μ))`.

Fields go through `FieldComparison.longFieldCode`: `iterate a ↦ (0,a,0,0)`,
`entry a λ μ ↦ (1,a,rawNoteEncode λ.1,rawNoteEncode μ.1)`. Rows go through `encodeBitRow`/`encodeRow`/
`encodeWeighted`, and tests through `encodeTest`.

## Deciders

- `limitCode n := decide (0 < n) && decide (encodedOrdinalFiniteRemainder n = 0)`.
- `properFieldCode`: tag 0 gives true. Otherwise: limit(upper), and (lower = 0 or limit(lower)), and
  `rawComparisonCode lower upper = 0`, meaning lt.
- `properOperandCode`: tag 0 gives true, otherwise `properFieldCode` of the field part.
- `admittedRowCode := admittedCode test && all operands proper`.
- `admittedClauseCode := all rows admitted`.
- `properClausesCode := filter admittedClauseCode`.

Reused, not rewritten:
- `OrdinalComparison.rawComparisonCode`, with `rawComparisonOrdinalCorrect` and
  `rawComparisonPrimitiveRecursive` (RawComparison* modules);
- `OrdinalComparison.encodedOrdinalFiniteRemainder`, with
  `OrdinalSuccessorProgram.classification` and `primitive` (OrdinalSuccessorProgram* modules,
  older ordinal round, listed in `verification/local-resume-2026-10-31/ordinal/PROMOTIONS.json`);
- `OrdinalComparison.rawNoteDecodeEncode` (RawNotationCode);
- `ActualBitFamilyRawClosed.admittedCode` (#1334).

## Statements

- `ExactLimitCode`: on the code of every `NONote`, `limitCode` is true iff `IsSuccLimit repr`.
- `ExactProperFieldCode`: on every field code, the decider is true iff `ProperField`.
- `ExactProperOperandCode`: the same for `properOperand`.
- `ExactAdmittedTestCode`: `admittedCode (encodeTest t) = true ↔ t.Admitted`.
- `ExactAdmittedRowCode`: on `encodeBitRow row`, iff `AdmittedOperandRow row`.
- `ExactAdmittedClauseCode`: on `rows.map encodeBitRow`, iff `AdmittedLiteralClause rows`.
- `ExactRawProperClauses`: `properClausesCode (encodeFamily family) = encodeFamily (properClauses family)`,
  a literal equation.
- `ExactOperandCodeInjective`: `LowerOperand.code` is injective.
- `ExactRawProperClauseEffectivity`: `Primrec` for all six deciders, plus `Computable properClausesCode`.

## Assumed / not claimed

Correctness is claimed only on codes produced by the typed encoders. On arbitrary naturals, for
example codes of non-normal raw notations or field tags ≥ 2, the deciders return some Boolean with no
semantic claim. This is the same convention as `longFieldCode` and #1334. Nothing about suppliers,
packets, or the rest of the emission program is claimed.
