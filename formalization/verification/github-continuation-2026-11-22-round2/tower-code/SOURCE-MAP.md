# Exact numerical coding of the native tower sequence

Reviewed base: `b28541e6f1682fc41c47a385729df36e9db87b0d` (rounds 3–5).

## Source and real scope

Paper 16 `16-persistent-marking-termination-ordering/sections/ordinals.tex:531–550` specifies the finite-type extractor terms (B)/(B_T). Lines 564–590 specify (D) and the actual native terms `t_n`; lines 634–647 state the height consequence. The existing `NativeTowerSequenceTargets.sequenceTerm` implements these literal expressions and #1462 proves closed-native realization of their semantic composites.

Round 5 #1470/#1471 fixes that explicit syntax family in `EffectiveCofinalFamily`, under the stated ordinal and upper-bound hypotheses. It does not assert `Computable` or `Primrec` of a numerical code family. The exact code gap is acknowledged in `verification/local-fable-pair-2026-11-22-round5/opusA/1470-SCOPE.txt` and `opusA/LEDGER.md`; choice-free structural Lean syntax definitions alone do not supply a Mathlib computability theorem.

The new result is unconditional numerical effectivity. It does not prove the external ordinal calibration, a BH endpoint identification, the inductive norm theorem, or an accessibility supplier. Conditional cofinality remains conditional on those separate interfaces.

## Existing encoding, preserved exactly

All Lean paths in this section are under `formalization/LogicLineages/NativeModule/PersistentMarking/`.

- `NativeSyntaxCountabilityTargets.lean:33–34`: `nativeCode q = ((tr q.val).map encodeTerm).getD 0`.
- `NumberedWindowOrdinaryTranslation.lean:14–29`: original constructors become ordinary constructors; original application heads remain ordinary heads; marked terms are rejected.
- `NumberedWindowArithmeticTermCode.lean:19–32`: literal constructor tags and all recorded type/head/argument fields.
- `NumberedWindowArithmeticHeadCode.lean:14–20`, `NumberedWindowArithmeticTyCode.lean:13–15`, `NumberedWindowArithmeticFields.lean:12–14,26–27`, and `NumberedWindowArithmeticPair.lean:11`: the existing polynomial pairing and finite field-list code.

`literalCode` is exactly the existing optional translation followed by that encoder. The numeric constructors in `NativeTowerCodeDefinitions` reproduce the existing tags and pair operations. No replacement semantic interpretation or arbitrary new Gödel numbering is used.

## Frozen target

New namespace: `LogicLineages.PersistentMarking.NativeTowerCode`.

New modules: `NativeTowerCodeDefinitions`, `NativeTowerCodeTargets`, and `NativeTowerCodeProof`.

1. `SequenceCodePrimitiveRecursive := Primrec sequenceCode`.
2. `SequenceCodeCalibration := ∀ n, literalCode (sequenceTerm n) = some (sequenceCode n)`.
3. `NativeCodeCalibration`: every closed native term with value `sequenceTerm n` has existing `nativeCode` equal to `sequenceCode n`.
4. `FullTowerCode`: the conjunction of these three unconditional statements.

The success equation in (2) excludes accidentally proving a primitive-recursive fallback-zero function. Statement (3) connects directly to the existing countability encoding used in the height development. No encoding instance on `Spine.Expr` is needed.

## Numeric program

`tierTypeCode` follows the literal type recursion. `wrapCode` builds the binder prefixes. `eraseTierCode` carries the shifted index explicitly, including the terminal bound occurrence. `iteratorCode` preserves the native recursor's original argument order. `natDownCode` and `downCode` use bounded iteration on a pair `(remaining depth, accumulated code)` to implement the descending application spines; their calibration equations will identify these loops with the existing structural recursions. The three fixed constants are coded through the existing translator and encoder, with successful translation established from their accepted closed-native syntax facts.

Primitive recursiveness uses only the pinned Mathlib `Primrec` arithmetic, pairing, `nat_rec`, `nat_casesOn`, and `nat_iterate` APIs. Calibration is to the current literal source definitions, without evaluating or normalizing the source terms.

## Preproof freeze and validation boundary

Definitions, targets, and this source map are written before the proof module. Their exact SHA-256 values are recorded in `LEDGER.md` before proof drafting. The root agent owns native gating and publication. No compiler, Git operation, accepted source edit, pin change, or numbered promotion is performed in this lane.
