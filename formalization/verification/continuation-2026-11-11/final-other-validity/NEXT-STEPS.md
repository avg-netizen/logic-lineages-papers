# Next original-leaf obligation, after the two exposures

The exact exposure packet stops at the original source and target leaves.
It does not supply transformed acceptance or primary/canonical transport.
All paths below are relative to `formalization/LogicLineages/`.

## What the exposed leaves actually are

`OriginalHereditaryValidity.normalizedData p.base` is literally
`InternalOriginalUniformContextMembership.normalizeData
(BottomParameter.baseData p.base)`. `normalizeData` changes only `member`.
Consequently its source/target leaves are literally
`BottomParameter.normalized p.base.oldSource` and
`BottomParameter.normalized p.base.oldTarget`.

`BottomParameter.normalized` branches on the original exact-bottom test.
It keeps the entire original output off exact bottom. At exact bottom it
calls the same old Program at `contextParameter`, which pairs the original
outer context with zero Gamma. Exposing these branch graphs does not prove
anything about changing a nonbottom raw term or its encoded Gamma.

## Actual leaf compiler and decoder chain

In `OrdinalComparison/TerminationOrdering/ID1Completion/`:

- `InternalOriginalUniformParameterLeavesDefinitions.lean` defines
  `parameterObject`, `decodedValue`, `sourceValue`, `targetValue`,
  `representativeValue`, and `Calibrated`.
- `parameterObject value parameter` runs the ORIGINAL
  `Encodable.decode` on `Nat.pair (Nat.unpair parameter).2 value`.
  `decodedValue` separately runs the ORIGINAL
  `Encodable.decode (OrdinaryArithmeticQuotient.Context n)` on the left
  parameter component and rejects a failed decode with zero.
- `sourceValue` then uses
  `NumberedNumericCarrier.rawCarrierTest n arity symbols S Gamma value`.
  In `NumberedNumericCarrierDefinitions.lean`, this is `decodeUniverse.isSome`;
  `decodeUniverse` filters `NumberedNumericDecoding.decodePackedNumber` by
  the mutual `universeTest` / `argumentsUniverseTest`.
- `targetValue` uses
  `NumberedUniformPackedDecoding.rawPackedDecode n arity Gamma value` and
  tests `isSome`. Its exact definition first checks
  `decodePackedNumber.isSome`, then retains the original `decodeType` and
  `decodeCode` outputs. `rawStructuralDecode` is the corresponding actual
  typed `decodeTerm` success check on an already raw type/code pair.
- `InternalOriginalUniformParameterLeavesPrimitiveProof` proves
  `decodedValuePrimitive`, `sourcePrimitive`, `targetPrimitive`,
  `representativePrimitive`, and `memberPrimitive`. Its exact codec
  suppliers are `OrdinaryArithmeticQuotientDecoderProof.contextDecoderPrimitive`
  and `JointGammaProgramsDecoderProof.objectDecoderPrimitive`. Source and
  target use `NumberedUniversePrimrecProof.rawCarrierPrimitive` and
  `NumberedUniformPackedDecodingProof.rawPackedDecoderPrimitive` respectively.
- `InternalOriginalUniformParameterLeavesProof.actualOriginalUniformLeafPrograms`
  invokes `GorbowPRProgram.Proof.allPrimitiveFunctions` FOUR separate times,
  obtaining `oldSource, oldTarget, oldRepresentative, member` together with
  their ALL-vector native evaluation equations. The compiler in
  `ComputabilityKnowledge/GorbowPRProgramProof.lean` calls private
  `programOfTextbook (Nat.Primrec'.of_prim h)`. Its only public conclusion is
  `exists p, forall v, evaluate p v = f v`, not an internal graph transport law.

## Actual global witness structure

`InternalOriginalUniformDescentSelectionProof.actualOriginalUniformDescentSelection`
obtains those four leaf witnesses and constructs
`data := Data.mk oldSource oldTarget oldRepresentative member`. It proves
its original generic selection laws and native calibration.

`UniformCertificateCompletion.GlobalSourcePackageProof.actualOriginalGlobalInputSelection`
then obtains that `base`, and independently obtains the actual `window`,
`oldSrc`, `oldComp`, `oldStep`, `oldVertex`, and `oldResult` witnesses. It
constructs the single record
`Inputs.mk base window oldSrc oldComp oldStep oldVertex oldResult` and the
conjunction `InputsCalibrated n arity p`.

`OriginalLambdaTraversalFinalGlobalProof.actualOriginalLambdaTraversalGlobalSelection`
obtains exactly such `p` and adds `Properties n arity p`. Those Properties
retain native preparation, the previous hereditary/global Package and the
independently proved SAME-final internal laws. They do not expose a new
structural correctness field for the opaque original leaf compilers.

## Concrete next lemma and scope discipline

The first unpaid graph-level supplier beneath the exposed target leaf is an
independent internal success/transport equation for the ORIGINAL compiled
`targetValue` chain: Object/Gamma parameter decoding, original
`rawPackedDecode` / `decodePackedNumber` and its typed recursive `decodeTerm`,
at the actual raw transformation and actual transformed parameter. The source
analogue must additionally transport the original `decodeUniverse` filter,
including its original head/window and argument-list checks.

Choose and prove a concrete original decoder/compiler witness with these
internal graph laws, or prove a joint existential supplier that carries
calibration AND those independently proved graph laws at the SAME leaf
witnesses. Do not assert the law for every `p` merely satisfying the existing
native `InputsCalibrated`; semantic evaluation equality is not an internal
reflection principle. Do not add the desired transport law as a new premise
or oracle and report the original theorem complete. Any later global
selection must retain the full previous Package with the strengthened,
proved witness, before quantifying over windows and runtime Gamma.

For the distinct representative/cancellation obligation,
`ContextUniformPrimary.representative` uses `List.range.findIdx` through
`classNumberTest`, `rawPackedDecode`, `primaryTest`, `primaryList`,
`reachable`, `step`, `vertices`, `candidates`, and `classCodes`.
`step` filters the pool by `NumberedExchangeCode.packedCodeExchange`, whose
actual recursive `codeExchange` includes head exchange, base permutations,
argument recursion, and fixed numbered labels/extra-list order. Transport
must be proved through these original functions. Primary equivalence alone
is not a strict quotient step and cannot pass the existing strict-step plus
representatives certificate checker.
