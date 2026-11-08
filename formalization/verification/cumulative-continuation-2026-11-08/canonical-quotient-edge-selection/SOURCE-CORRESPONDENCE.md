# Canonical quotient-edge selection and typed propagation: frozen prerequisite

This packet freezes five supporting targets toward paper 06 `lem:id1`.
It contains definitions, target propositions, preflight aliases and source
pins only. Independent static review must precede native preflight and proof
authorship. No compiler, proof implementation, Git action, accepted-source
edit, target-register change or numbered-source promotion is included.

## Original source and exact scope

Paper 06, `06-godel-t-termination-ordering/paper.tex`, lines 537-556, fixes a
finite subtype-closed type window, the original typed numbered reduction,
function-side auxiliary-application reduction, primary equivalence and the
least-code quotient representatives. Lines 563-588 use the arithmetic edge
relation with typedness and function-side application in the accessibility
argument. The present targets select a particular calibrated quotient-edge
checker and establish a local typed-propagation prerequisite. They do not
complete the application quotient-edge lift, path lift, computability descent,
`CertifiedApplicationLift` or the closed all-term accessibility theorem.

The original all-input numeric functions remain
`NumberedNumericStep.numericStepTest`,
`NumberedNumericQuotientEdge.numericEdgeTest` and
`InternalOriginalTypedCarrier.typedValue`. No successful decode, canonical
input, accepted-step restriction or encoded external type is inserted into
their calibration domains. Every fixed original finite signature, symbols,
window, ambient context and precedence table has its original domain.
Subtype closure is required only for external calibration and the shared
selection, not for either internal derivation target.

## One existing Data and one step-leaf update

The packet uses `InternalCanonicalDescentSelection.Data` unchanged. Its only
fields remain `oldValidity`, `member`, and `oldEdge`; there is no new record,
old typed field, correctness field, invariant field or lift field.

For one such `data`, the literal definitions are:

- `baseData.oldValidity = data.oldValidity`;
- `baseData.member = data.member`;
- `baseData.oldStep = data.oldEdge.stepProgram`;
- `R = data.oldEdge.targetRepresentative`;
- `V = (InternalCanonicalDescentSelection.validity data).sourceValid`;
- `W = conjunction (InternalOriginalApplicationStep.stepChecker baseData)
  (composition V projection1)` on `[rawSource, rawTarget, rawStep]`;
- `selectedData = { data with oldEdge := { data.oldEdge with stepProgram := W } }`;
- `edgeData = InternalCanonicalResultFoldCalibration.edgeData selectedData`;
- `Edge = InternalQuotientEdgeChecker.checker edgeData`.

The second conjunct of W is precisely **source** validity applied to the raw
target. It is not the old packed-target validity, output validity, a selected
representative test, or a guard around the final edge endpoint. W contains
exactly these two conjuncts. No H guard is needed or added.

Changing `oldEdge.stepProgram` changes none of the definitions which depend
only on `oldValidity`, `member`, and `oldEdge.targetRepresentative`.
Consequently R, V, the checked descent transition T, fallback descent D,
canonical opening G, combine C, actual finite fold N, actual good-run H and
the selected canonical typed checker remain definitionally unchanged.
In particular C is still D after the **original raw application**, and N
still uses the original `2 * originalPayload + 1` fuel and original fallback.
Neither an old combine nor a repacked-codomain application is substituted.

The source representative of the selected edge data is still the exact-one
branch `if V(input)=1 then N(input) else 0`. Its target representative is N
on **every** input. The added raw-target check in W does not redefine that
target representative as a source-universe-filtered function. Malformed and
decoded-but-nonuniverse target inputs retain the original target behavior in
the all-input representative calibration.

`typedAccepted data value typ` is the existing canonical descent acceptance
at R/V/member, with `typ` the requested type coordinate. Its four exposed
factors are member(typ)=1, V(value)=1, left(value)=typ and T(value)=value.
The old canonical typed AST is not imported as an opaque additional conjunct;
H-, N-, D- and R-fixed conditions are not added to this checker.

## The five frozen targets

0. **ActualOriginalCanonicalEdgeStepCalibration.** Under the original
   all-input leaf calibration and subtype closure, W equals the unchanged
   numeric step test on every natural triple.
1. **ActualOriginalCanonicalEdgeDataCalibration.** Under the same hypotheses,
   W, the existing fold-edge data at `selectedData`, its recursive validity
   and canonical typed carrier, and the actual final Edge program satisfy
   their original full-input calibration interfaces. The final Edge equation
   explicitly names `numericEdgeTest` on every natural input triple.
2. **ActualOriginalCanonicalEdgeApplicationStep.** For arbitrary Data,
   positive body, variable type, derivation context Delta and symbolic terms,
   derive W(sourceApp,targetApp,liftedStep) from exactly the existing
   `InternalOriginalApplicationStep.liftPremises baseData` and W(s,t,k).
3. **ActualOriginalCanonicalEdgeTypedPropagation.** For arbitrary Data, body,
   variable type, Delta and symbolic x,y,certificate,typ, derive
   typed(y,typ) from exactly typed(x,typ) AND Edge(x,y,certificate).
   No additional membership, raw selector, tag, validity, calibration,
   subtype-closure, H or target-typed premise is permitted.
4. **ActualOriginalCanonicalEdgeSelection.** At each original fixed finite
   signature/window/context/table with subtype closure, select ONE existing
   Data satisfying original leaf calibration, the complete selected
   calibration and both internal laws. That selection precedes every body,
   variable type, derivation context, symbolic type and certificate.

`InternalLaws data` is a conclusion containing targets 2 and 3 at this fixed
data. It is neither a Data field nor an assumed supplier. Preflight aliases
name all five propositions once each; no alias proves a proposition.

## External calibration route and its limits

This is a specification-level supplier plan, not a proof implementation.

`InternalOriginalApplicationStepEvaluationProof.selectedCalibration` gives
the all-input calibration of the base guarded application step, its endpoint
and recursive validity from exactly the three original base leaves.
`InternalCertifiedSourceGuardSelectionEvaluationProof.originalStepTargetUniverse`
proves that an accepted original numeric step has a source-universe target
under the original subtype-closure hypothesis. Thus V(target)=1 is redundant
when the original step accepts; when it rejects, W's first conjunct already
rejects. These cases cover every natural triple, not just a valid domain.

Only that already proved source fact is reused from the older certified
selection. Its old typed checker, H guards, fold-fixed checker and larger Data
interface are not reused. In particular
`InternalTypedEdgePresentationSupportProof.presentation` must NOT be used as
the new internal presentation: it depends on the old typed interface.

W calibration supplies the updated step field's original calibration.
The other fields are unchanged. Apply the existing canonical fold data
calibration to `selectedData`, then consume the existing quotient checker
calibration to obtain the explicit final Edge equation. The already checked
canonical descent leaf-existence supplier gives one shared Data selection.
No semantic evaluation equality is used as an internal inference rule.

## Internal W application closure route

Both Data and the internal terms are arbitrary. Recover the two actual W
conjunct graphs with the original arithmetic conjunction laws. The first
is exactly base-step acceptance; the second is V(t)=1.

Use `InternalOriginalApplicationStepSupportProof.applicationStep` with the
unchanged `liftPremises baseData` and base-step acceptance to derive actual
base-step acceptance at the two original raw applications and the original
lifted certificate. This supplier already proves the new source validity and
packed-target validity required by its original outer guard, but those facts
alone are not treated as the new target **source** validity.

The existing endpoint inside liftPremises is decoded using
`InternalStructuralEndpointGuardSupportProof.endpointRecover`. It supplies
the original function/target arrow tags, argument domain tag, argument V
graph and codomain membership, together with the actual arrow constructor
graph already in liftPremises. Combine these with W's V(t) and the original
target-application graph. The checked
`InternalCanonicalResultFoldInvariantApplicationSupportProof.rawValidity`
then closes **both** concrete recursive validator branches at targetApp,
giving V(targetApp)=1. Recombine the two actual W conjuncts at the lifted
inputs. No newly assumed application-closure theorem or external source
decoding is needed.

The existing endpoint constructor
`InternalStructuralEndpointGuardSupportProof.endpointAccept` also takes
only those original graph requirements and the arrow graph, with no old
typed dependency. It remains an admissible supplier if endpoint assembly is
needed later; this frozen application target already supplies the actual
endpoint through its unchanged liftPremises.

## Internal typed propagation route

The final target quantifies no raw source, raw target or raw step witnesses.
The actual original certificate must be unpacked internally using Program
totality/continuations for its source, target and step selectors. The existing
`InternalAcceptanceSupportProof.programCases` supplies these bound outputs,
with capture-avoiding relabeling of the original context and conclusion.
No external certificate decoder or natural-number soundness theorem may
introduce these witnesses into the internal calculus.

At those actual selector graphs,
`InternalQuotientEdgeCheckerSupportProof.checkerRecover` yields W(s,t,k),
the actual source-branch graph with output x, and N(t)=y. Recover W's V(s),
V(t) and its original raw-tag guard from the actual conjunction ASTs.
The source V(s)=1 graph selects N in the source representative's exact-one
branch, so the source graph becomes the actual N(s)=x graph. No inference
from an external equality of representative functions is permitted.

Internally query the original left selector at s, obtaining a symbolic raw
tag u with left(s)=u. Apply the existing actual-N output consumer
`InternalCanonicalResultFoldInvariantConsumerProof.actualOriginalCanonicalFoldOutputConsumer`
to V(s), left(s)=u and N(s)=x. Its conclusion supplies left(x)=u and the
other output invariants; any H conclusion is a proved output, not a guard
or premise of this packet.

Independently recover typed(x,typ)'s factors using
`InternalCanonicalDescentSelectionInternalProof.typedRecover`. It supplies
left(x)=typ and member(typ)=1. Functionality of the actual original left
Program identifies u with typ. Transport the source-tag graph along this
internal equality. Then
`InternalOriginalStepGuardSupportProof.taggedRecover`, applied to the first
W conjunct, transfers that same raw tag from s to t. Equivalently one may
recover both raw tags and their original guarded equality; neither equality
is an external semantic assertion.

Now V(t), left(t)=typ, member(typ)=1 and the actual N(t)=y graph are available.
Consume the checked
`InternalCanonicalResultFoldInvariantConsumerProof.actualOriginalCanonicalFoldTypedOutput`
to derive the existing typed(y,typ), discarding its additional H conclusion.
Eliminate every internally bound selector/tag witness back to the original
context. Membership is recovered from the source typed checker rather than
inferred from arbitrary V or requested as a new premise. The requested typ
remains symbolic throughout; no finite-window member enumeration, type-code
numeral evaluation or external calibration is used in this derivation.

## Freeze, provenance and verification boundary

The only new Lean files are `InternalCanonicalQuotientEdgeSelectionDefinitions`,
`InternalCanonicalQuotientEdgeSelectionTargets` and
`InternalCanonicalQuotientEdgeSelectionPreflight`. Existing accepted source,
specification and dependency bytes are preserved. No proof file, theorem
implementation, added axiom, admitted term or unsafe/native proof shortcut is
created. Static text/import/hash checks are not native elaboration.

`FROZEN-SOURCE-PINS.json` hashes the three specification files and this source
correspondence. `SOURCE-PINS.json` pins the transitive local import closure
of these files and the prospective checked suppliers, including meta imports,
plus the source paper, toolchain/checker inputs and accepted supplier evidence.
`FROZEN-SPECIFICATION.json` records target names, exact AST boundaries, scope,
resource limits, counts and hashes of both pin maps. This inventory is not
itself a source-matched native closure receipt or a proof acceptance claim.

Any later native preflight or proof run requires the coordinator's explicit
release and sole compiler-slot grant, using only `scripts/check.py` under the
unchanged profile: 2048 MiB heap, 1536 MiB process-tree RSS, 2048 MiB minimum
free memory, one thread, 90 CPU seconds, 180 wall seconds and existing upstream
cache only. Allowed final axiom closure is exactly the usual propext,
Classical.choice and Quot.sound foundations. The current deadline is
2026-11-08 18:00 UTC; this freeze does not authorize work past it.

No full application quotient-edge lift, path lift, joint-context compiler,
outer pathValue wrapper, CertifiedApplicationLift, multiset/constructor/
lambda/substitution closure, all-term endpoint, lem:id1 completion, numbered
source promotion, full-root build, remote CI or publication is asserted.
