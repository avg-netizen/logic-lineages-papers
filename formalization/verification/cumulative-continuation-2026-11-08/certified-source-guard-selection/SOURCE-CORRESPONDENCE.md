# Certified source-guard selection

This four-target supporting packet for paper 06, `lem:id1`, freezes explicit
selected source guards after the original representative normalizer. It does
not complete application compatibility, a quotient-edge/path lift, or the
numbered accessibility lemma. Definitions, comparators and this correspondence
precede all proof authorship. Independent review and native preflight remain
required. No existing frozen source is edited.

## Original source and shared leaves

`06-godel-t-termination-ordering/paper.tex`, lines 537–549, fixes the finite
subtype-closed type window and original function-side auxiliary application
rule. Lines 551–556 fix finite primary equivalence classes, the least-code
representatives, the quotient one-step relation and its positive closure.
Lines 558–560 state the full arithmetic accessibility lemma, still pending.

The new `Data` stores only four groups of finite original Program leaves:
`oldValidity`, `member`, `oldEdge`, and `oldTyped`. There are no proof fields.
All selected ASTs are determined by these leaves before any positive body,
variable type, source type, symbolic term, endpoint, or certificate is chosen.

Write:

- V = `InternalApplicationValidityStack.recursiveData oldValidity member`.
- B = `InternalOriginalApplicationStep.stepChecker baseData`, with
  `baseData = { oldValidity, member, oldStep := oldEdge.stepProgram }`.
  This is exactly the original outer-guarded normalized application-step AST.
  Its endpoint is the existing structural endpoint on V and the same member.
- N = `InternalRepresentativeFoldCalibration.normalizer oldValidity member oldEdge`.
- G, L, C are that same representative-fold `rootGuard`, `leaf`, and `combine`.
- H = `InternalApplicationCertifiedResultFoldClosure.goodRun G L C`.
  It checks the same run used by N, at its own unchanged
  `2 * original-payload + 1` fuel, with status one, empty work and one result.
- F = `InternalRepresentativeFoldCalibration.foldedData oldValidity member oldEdge`.
- E = `InternalRepresentativeTag.withRepresentatives V F`.
- T = `InternalTypedEdgePresentation.typedChecker V member oldTyped`.
  This keeps the original canonical typed leaf, V.sourceValid(value), the
  original raw outer-type equality, and membership of the supplied type code.

The selected step is the literal exact-one conjunction

`B(s,t,k) AND V.sourceValid(t) AND H(s) AND H(t)`.

The selected quotient-edge Data has this step and exactly E's two
representative fields. E's source uses V.sourceValid; E's target uses
V.targetValid, which is still packed validity alone. There is no global
replacement of packed-target validity by universe validity. Only accepted
selected steps expose the extra source-validity graph of their raw target.

The selected typed checker, with input order `[value,type]`, is the literal
exact-one conjunction

`T(value,type) AND H(value) AND equalityTest(N(value),value)`.

The fixed-point test is the existing original numeric equality-test AST,
composed with N at coordinate zero and the same original value projection.
H and N are the same Programs in the step, typed and representative wrappers.
No independent existential normalizer is selected at a later type or term.

## Four frozen targets

1. `ActualOriginalCertifiedSourceGuardCalibration` starts from all-input
   calibration of those original leaves and subtype closure of S. It proves
   all-input calibration of the original selected V/endpoint/B package,
   strengthened edge Data (step and both representatives), strengthened
   typed checker, and final original quotient-edge checker. There is no
   successful-input or successful-decoding premise restricting calibration.
2. `ActualOriginalCertifiedStepAcceptanceFactorization` is an internal iff
   between output-one acceptance of the literal selected step and the four
   actual graphs B(s,t,k)=1, V.sourceValid(t)=1, H(s)=1, H(t)=1.
3. `ActualOriginalCertifiedTypedAcceptanceFactorization` is an internal iff
   between output-one acceptance of the literal selected typed checker and
   the actual graphs T(value,type)=1, H(value)=1, N(value)=value.
4. `ActualOriginalCertifiedSourceGuardSelection` chooses ONE shared leaf
   record for each fixed original signature, subtype-closed window S,
   ambient Gamma and precedence table. The selected calibration is before
   every internal body, variable type and symbolic term. Both factorizations
   hold for the exact same selected Programs, not newly selected witnesses.

The two internal targets quantify arbitrary Program leaves and symbolic
terms. They have no subtype-closure, calibration, universe, canonicality,
successful-run, representative-congruence or lift hypotheses. Their
conclusions are actual Derivation objects of the original internal calculus.

## External redundancy and calibration route

The original guarded application-step calibration already proves that B is
the unchanged numeric step function on every natural triple, for arbitrary
windows. On an accepted B input, the existing
`NumberedNumericStepProof.numericStepSound`, using subtype closure, gives
both original decoded endpoints in the universe. In particular the original
source-validity test accepts raw target t. This is the sole additional
target-universe guard and its semantic redundancy is restricted to the
accepted-step situation; nothing changes global target representative behavior.

`InternalApplicationCertifiedResultFoldClosureProof.actualOriginalResultFoldGoodRunCalibration`
gives H(value)=1 externally on all natural inputs for these exact G/L/C.
Its three-target focused exact gate now has an `ACCEPTANCE.json`; that record
still reserves final independent checkpoint review to the coordinator. This
packet pins the checked supplier and its exact alias, not an assumed theorem
field. It does not reflect external H calibration into an internal derivation.

The checked membership/canonical typed wrapper gives T's all-input original
semantics. At original typed acceptance, `typedCanonicalCarrierTest` supplies
an original universe decode q and `representativeCode symbols S q = value`.
The checked representative-fold calibration identifies N on every natural
input with the unchanged original packed-target representative. Universe
decoding retains the same packed decode, so N(value)=value at this accepted
canonical value. No internal normalizer type invariant or congruence is needed
for this external calibration argument. Rejected and malformed typed inputs
stay zero because the unchanged canonical wrapper is an explicit conjunct.

The selected representative fields use the existing calibration of F and
the checked tag-wrapper calibration at V. Updating only the step field then
gives calibrated edge Data; the original quotient-edge checker calibration
supplies its complete all-input numericEdgeTest equation. Existing finite
Program existence theorems supply the four shared leaves before the internal
quantifiers in the fourth target.

## Internal factorization route and exact boundary

The existing internal exact-one conjunction acceptance theorem handles each
explicit conjunction. Original composition and projection graph rules expose
the unary checks at the required coordinates. For the fixed-point factor,
the internal equality-test acceptance theorem, actual N graph totality and
functionality, and object-language equality substitution convert the composed
equality check to the actual graph N(value)=value and back.

These are syntactic/internal graph arguments for arbitrary Programs. External
all-input H=1 and external canonical representative equality cannot be used
as internal inference rules. In particular neither H nor the fixed-point
graph is deleted from the factorized formulas.

This packet does not assert internal representative application congruence,
target dispatch, strengthened-step application preservation, combined
quotient-edge compatibility, path preservation, context-uniform selection,
the outer pathValue malformed-input wrapper, CertifiedApplicationLift,
multiset/constructor/lambda/substitution arguments, or all-term accessibility.
The separate local representative-congruence packet is not a dependency or
an extra premise here. Later edge/path assembly must prove its actual local
compatibility rules rather than add them as assumptions.

No claim is made for the strengthened step on a non-subtype-closed window.
The original fallback programs and a piecewise fixed-window selection must
be treated honestly in a later packet; this one does not select a replacement
for those windows or claim an effective uniform compiler.

No proof author or native compiler has run for this packet. No compiler slot,
Git operation, upstream rebuild, numbered-source promotion, full-root build,
remote-CI result or publication is claimed.
