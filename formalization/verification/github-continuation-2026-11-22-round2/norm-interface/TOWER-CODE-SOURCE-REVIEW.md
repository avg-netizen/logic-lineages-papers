# Independent source review of the native tower-code packet

Continuation date: 2026-11-22 (America/Chicago).
Reviewed source base: `b28541e6f1682fc41c47a385729df36e9db87b0d`, plus the
new frozen `NativeTowerCodeDefinitions` and `NativeTowerCodeTargets` files.
All short Lean filenames below are under
`LogicLineages/NativeModule/PersistentMarking/`.

## Verdict

No material source-correspondence or assumption defect was found. The target
asserts primitive recursiveness of a particular natural-number code function
and calibrates it to the existing literal encoding of the actual printed
family. It does not merely assert primitive recursiveness of an unrelated
surrogate sequence, and it does not add a coding premise to the ordinal
theorems. Native validation remains the proof-validity gate; this review does
not repeat the proof-body audit.

## The code represents the original syntax

`NativeTowerCodeDefinitions.lean:13-19` defines

```text
literalCode q = (NumberedWindowOrdinaryTranslation.tr q).map encodeTerm
fixedCode q = (literalCode q).getD 0
```

The imported `tr` preserves ordinary source constructors, including original
application heads, and rejects marked expressions
(`NumberedWindowOrdinaryTranslation.lean:10-25`). The imported `encodeTerm`
retains the literal type, head, and argument fields with their established
tags (`NumberedWindowArithmeticTermCode.lean:15-30`). The packet introduces no
new quotient or alternative semantic coding of a term.

The numerical constructors match those existing encodings:

| New definition | Existing syntax/encoding correspondence |
|---|---|
| `consCode`, `node2Code`, `arrowCode` | The polynomial `pair` and field-list encoding, and the ordinary arrow-type encoding (`NumberedWindowArithmeticPair.lean:11`, `NumberedWindowArithmeticFields.lean:12-14,26-27`, `NumberedWindowArithmeticTyCode.lean:13-15`). |
| `boundCode`, `lamCode`, `headCode` | Existing term tags 1, 2, and 4 with two literal fields (`NumberedWindowArithmeticTermCode.lean:21-24`). |
| `appCode` | The ordinary application head's tag 4 and its two actual type parameters, followed by the ordered two-element argument list (`NumberedWindowArithmeticHeadCode.lean:19`). It is not the auxiliary-application constructor. |
| `tierTypeCode`, `bindersCode`, `eraseTierCode` | The literal tier types, outer-to-inner binder order, and shifted terminal bound index used by the native tower and iterator definitions. |
| `natDownCode`, `downCode` | The descending application spines of `NativeTowerTargets.natDown` and `NativeTowerSequenceTargets.downTerm`. Each iteration decreases the remaining depth once; its argument type and tower index match that depth. |
| `sequenceCode` | The zero, one, and `l + 2` branches of `NativeTowerSequenceTargets.sequenceTerm` (`NativeTowerCodeDefinitions.lean:105-111`; `NativeTowerSequenceTargets.lean:43-48`). |

The three `fixedCode` constants are finite expressions for the existing
`ordinalFix`, `ordinalNext`, and `omegaCarrier`. Their use does not introduce
a semantic ordinal computation or an external ordinal assumption.

## The calibration target excludes fallback-only success

`NativeTowerCodeTargets.lean:12-25` contains three unconditional propositions:

1. `Primrec sequenceCode` for the actual defined function.
2. For every `n`, `literalCode (sequenceTerm n) = some (sequenceCode n)`.
3. For every signature and closed native term of outer type `indexType`
   whose syntax is `sequenceTerm n`, its existing `nativeCode` equals
   `sequenceCode n`.

The second proposition is a successful optional-translation equality. It
cannot be satisfied merely by returning the fallback zero on a failed
translation. The third proposition uses exactly
`NativeSyntaxCountabilityTargets.nativeCode`, whose definition at lines 33-34
is the same translation/encoding followed by `getD 0`. Its term argument
retains closed-native typing, and the equality is independent of the proof
used to construct the subtype.

The established encoding already has a literal decoder and an exact
roundtrip target (`NumberedWindowArithmeticTermCode.lean:63-81`;
`NumberedWindowArithmeticTermCodeTargets.lean:41-44`). Thus the numerical
effectivity statement uses the repository's syntax representation rather
than requiring an unprovided `Primcodable Spine.Expr` instance.

## Manuscript and integration scope

The paper fixes the native realizers of (D) at
`16-persistent-marking-termination-ordering/sections/ordinals.tex:567-591`.
`paper.tex:112-113` requires an effective cofinal family of closed native
terms of outer type `o → o`. The code target identifies that family, and
primitive recursiveness is a precise sufficient effectivity property of its
syntax codes. It makes no claim that term ranks, arbitrary semantic ordinals,
or a cofinal witness chosen from an ordinal input are computable.

The separate `ConditionalMain16UniformEffectiveCodedTargets.lean:19-38`
retains the literal `sequenceTerm` witnesses, their closed-native subtype,
strict rank cofinality, and upper bounds, and additionally records the
`nativeCode` equality and `Primrec sequenceCode`. Its five hypotheses remain
the norm theorem, uniform closed-theory accessibility, calibration, tower
hypotheses, and BH identification. The unconditional coding results supply
the new code fields; they are not sixth or seventh external hypotheses.

This review supports acceptance of the coding packet at its frozen scope
once its exact native/axiom gate passes. It does not promote any numbered
ordinal statement or discharge the retained ordinal-analysis premises.
