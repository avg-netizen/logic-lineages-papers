# Original uniform parameter leaves: frozen prerequisite

This packet freezes three specification modules and three exact targets only.
No proof authorship, compilation, acceptance or numbered-source promotion is
claimed. It supplies the previously missing global binary-leaf selection for
the parameterized validity/descent programme, without changing its targets.

## Literal source and codecs

Paper 06, `06-godel-t-termination-ordering/paper.tex`, lines 537-549, fixes the
original typed reductions and finite subtype-closed window. Lines 551-556
specify primary equivalence, least-code representatives and arithmetic H/R;
lines 558-560 state `lem:id1`. These leaves are supporting coding prerequisites,
not proofs of internal closure, canonical-fold correctness or accessibility.

The ONE parameter is literally
`Nat.pair (OrdinaryArithmeticQuotient.contextCode symbols S table)
(Encodable.encode Gamma)`. The first component uses the unchanged ORIGINAL
Context decoder, including Encodable.finPi table coding. The primitive
library's different finArrow table encoding MUST NOT be substituted.
Gamma is recovered ONLY through the original ContextUniform.Object decoder
on `Nat.pair (Nat.unpair p).2 value`. No new Gamma decoder, exported instance,
source semantics, successful-decode domain or object payload is introduced.
All four leaves preserve the original zero default when Context decoding
fails. Object decoding is the original total pair codec; the codec target
proves totality with its second component exactly the supplied whole value.

Source validity retains the original rawCarrierTest and universe filter.
Target validity and target representative use rawPackedDecode WITHOUT a
universe filter. Raw representative is the original ContextUniformPrimary
representative, already calibrated to the original least representative.
Membership uses the original decodeType and original membershipValue, with
the input a numeric type code. Every Program gets [value,p], including member
at [type,p]. Symbol/type/context lists and table are never captured first.

## Three frozen targets

1. ActualOriginalUniformParameterCodec: exact context/Object round trips at
   parameterCode, plus original Object totality at ALL raw parameters while
   retaining the supplied value. No codec replacement is permitted.
2. ActualOriginalUniformLeafCalibration: on ALL binary vectors, each raw leaf
   equals the same decoded wrapper around its ORIGINAL fixed-window value.
   Failed packed decodes and malformed context parameters remain in scope.
   This is external numeric equality, not evaluation-to-derivability reflection.
3. ActualOriginalUniformLeafPrograms: forall n/arity, exists FOUR Program 2
   ASTs, THEN forall symbols/S/Gamma/table/value. The shared tuple is calibrated
   on ALL raw vectors and agrees on every exact parameterCode slice with the
   original sourceValidityValue, targetValidityValue, targetRepresentativeValue
   and membershipValue. No PR, calibration, success, hS or window premise is
   supplied. The available original representative calibration needs no hS,
   so the stronger arbitrary-window statement is intentional and justified.

## Existing proof suppliers, no general PR reproof

- NumberedUniformPackedDecodingProof.rawPackedDecoderPrimitive and
  rawPackedCalibration give the original target decoder and raw/typed bridge.
- NumberedUniversePrimrecProof.rawCarrierPrimitive gives joint source validity.
- ContextUniformPrimaryPrimitiveProof.actualRawRepresentativePrimitive and
  ContextUniformPrimaryCalibrationProof.actualRawRepresentativeCalibration
  give the ORIGINAL raw representative and exact least-code correspondence.
- OrdinaryArithmeticQuotientDecoderProof.contextDecoderPrimitive is required
  for the ORIGINAL context/table codec. Never use generic Primrec.decode here.
- JointGammaProgramsDecoderProof.objectDecoderPrimitive gives the ORIGINAL
  Object decoder. JointGammaDomainCodecProof.actualObjectCodec gives totality
  and original objectCode inverse; pair injectivity retains the raw value.
- NumberedTypeCodecPrimrecProof.typeDecoderPrimitive and
  NumberedHeadWindowPrimrecProof.memberPrimitive provide type membership.
  InternalStructuralEndpointGuardEvaluationProof shows the established route.
- Existing Primrec pairing, projections, option-map/getD, Boolean conversion
  and composition close each binary function. Existing Proof.allPrimitiveFunctions
  selects each Program ONCE at arity two, before any finite window is given.

The parameterized validity fold consumes the source/target/member slices as
its existing external calibration premises. Parameterized descent can consume
the representative slice. This packet does not identify a selected canonical
fold AST with the old least-code representative, prove its internal congruence
or closure, or claim those later consumers have already been assembled.

## Freeze and required gates

FROZEN-SOURCE-PINS.json pins the new three Lean files and this correspondence.
SOURCE-PINS.json pins the full local import closure of the new files and exact
existing supplier roots, plus manuscript and unchanged build inputs.
STATIC-CHECKS.json is only static source/hash checking, never Lean elaboration.
Independent review must precede proof authorship. Comparator preflight and exact
aliases with actual standard-axiom audits require a fresh coordinator slot.

No compiler or Git action was taken. Existing limits remain 2048 MiB heap,
1536 MiB RSS, 2048 MiB minimum free, one thread, 90 CPU seconds, 180 wall seconds,
pinned upstream cache and scripts/check.py. Hard cutoff is 2026-11-08 18:00 UTC.
Only propext, Classical.choice and Quot.sound are allowed. There is no added
axiom, sorry/admit, oracle, internal reflection, canonical/path completion,
CertifiedApplicationLift discharge, constructor/lambda/substitution proof,
all-term accessibility, lem:id1 completion, source-register change, dependency
or CI change, full-root build or publication claim.
