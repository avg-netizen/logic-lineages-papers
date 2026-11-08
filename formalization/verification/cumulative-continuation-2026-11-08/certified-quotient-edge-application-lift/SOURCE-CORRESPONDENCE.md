# Local original certified quotient-edge application lift

This specification is a local supporting component for paper 06, `lem:id1`.
It connects the already frozen certified source-guard selection and internal
representative application-congruence contracts to the original quotient-edge
core. It does not assert their unfinished proofs are already checked. No
uniform path, outer typed-edge or whole accessibility result is claimed.

## Same selected data and original programs

The only data type is an abbreviation of
`InternalCertifiedSourceGuardSelection.Data`. There are no added proof fields
and no independent choice of validity, normalizer, success test or representative.
Write V, N, H and C for the exact selected recursive validity, normalizer,
good-run and `InternalRepresentativeFoldCalibration.combine data.oldEdge`.
These names explain the source programs; no new AST is substituted for them.

The selected step is the conjunction of the already checked original guarded
application-step checker, V.sourceValid at the raw target, and H at both raw
endpoints. The representatives are exactly the tagged folded representatives
from the same leaves. Their source/target validity wrappers remain distinct.
The selected typed checker retains the old canonical typed/membership wrapper
and explicitly checks H(value) and the actual graph N(value)=value.

`coreAccepted` is literally `InternalQuotientEdgeChecker.accepted (edgeData
data)`. It is not the outer `InternalQuotientEdgeTypeGuard` checker. The raw
quotient certificate is the original source paired with (target paired with
step). The original step lift prefixes the original appFunction position.
The `edgeLift` program has arity FOUR with input order
`[domain,codomain,argument,certificate]`. C also has arity FOUR, with input order
`[domain,codomain,functionOutput,argumentOutput]`.

The definitions import only `InternalCertifiedSourceGuardSelectionDefinitions`.
Targets imports only these definitions; the comparator-only preflight imports
only Targets. The frozen specifications of the two unfinished suppliers are
pinned, not their live candidate proof files. Existing checked supplier APIs
are separately pinned for the proposed proof route. No existing source is edited.

## Four exact targets

1. **ActualOriginalCertifiedApplicationStepClosure.** For arbitrary shared
   leaves, the original endpoint/application/step-lift graph premises, selected
   child step acceptance and the actual H(argument)=1 graph imply selected
   parent step acceptance. This small prerequisite does not assume argument
   canonicality or calibration. It must prove the extra source-validity and
   parent-success guards that the checked base rule alone does not discharge.
2. **ActualOriginalCertifiedEncodedQuotientEdgeApplicationLift.** The shared
   selected typed source at sigma->tau, selected typed argument at sigma,
   accepted core edge x,y,c, and exact C outputs at x,a and y,a suffice given
   the literal original edge/application/step constructor graphs for the raw
   child and lifted certificate. No raw tags, raw validities, endpoint acceptance,
   parent success, argument fixed-point or representative congruence are added
   as assumptions. All opened witnesses are actual Program graphs.
3. **ActualOriginalCertifiedQuotientEdgeApplicationLift.** The same core
   premises plus the actual original `graph4 edgeLift lifted d e a c` imply
   core acceptance at the two given C outputs and that same lifted certificate.
   No raw witnesses or selectors are exposed in this final interface.
4. **ActualOriginalSelectedCertifiedQuotientEdgeApplicationLift.** One shared
   data selection for the fixed original signature, subtype-closed finite S,
   Gamma and precedence table precedes every body, source type and symbolic
   term. It retains both original and selected all-input calibrations and
   proves target 3 for that exact selection. It does not choose a fresh
   representative or normalizer after seeing the types or terms.

The two middle targets assume only calibration of the membership leaf and
subtype closure outside the internal formula. These are used exclusively for
closed type-code calculations: an accepted arrow membership supplies codomain
membership. If the closed arrow is absent from S, the checked closed numeral
graph at zero and actual output-one graph yield an internal contradiction by
functionality. No semantic calibration on a symbolic endpoint is reflected
into an internal derivation. The selected final package supplies this leaf
calibration from its unchanged all-input original calibration.

## Required derivation route, not additional hypotheses

First factor the selected typed and step acceptance using the frozen
`InternalCertifiedSourceGuardSelection` contracts. Recover base typed member,
source-validity and raw-tag graphs, H(argument), and N(argument)=argument.
Decompose the accepted core at actual original certificate selectors, recovering
selected raw-step acceptance and the two exact representative graphs.

Use source validity from the base step and representative tag transport to
move the typed representative source tag backward to the raw source. Original
guarded-step tagged acceptance then gives the raw target tag and packed target
validity. The actual argument typed guard gives source validity and its raw
domain tag. The checked closed arrow graph and closed codomain-membership
computation reassemble the structural endpoint. Thus the existing typed-edge
presentation proof route applies to these SAME selected AST components; its
separately existentially chosen data must not be substituted.

For selected-step closure, apply the already checked
`ActualOriginalGuardedApplicationStep` to get base parent acceptance. The
ordinary recursive endpoint application-validity rule gives source-parent
source validity and target-parent packed validity. To obtain target-parent
SOURCE validity, rebuild the structural endpoint on `(t,t,a)` using the extra
selected raw-target source-validity graph, the same recovered target tag,
argument validity and member graph. Its source application is the original
target application. Apply the checked recursive endpoint closure again, with
both application outputs that same target application. No source-universe
restriction is inserted into the globally defined target representative.

For EACH parent H graph, bind actual N outputs of its function and argument
using internal Program totality, then bind the actual C output of those N
outputs. Child H acceptance plus those actual N graphs gives the certified
child folds. Reconstruct original typed constructor graphs from the derived
tags, internally bound right selectors and original pair inverse/application
equations. The parent source-validity graph is exactly the fold root guard.
Apply checked certified-fold application closure at the unchanged own parent
fuel and retain the parent H graph. External goodRun=1 calibration is NOT an
internal supplier here. Argument fixed-point acceptance is unnecessary for
this success-only prerequisite.

For the source representative, use the same source-valid function and parent,
child H graphs, actual N(argument)=argument, original constructor graphs and
given C(d,e,x,a)=out in the frozen source representative congruence contract.
For the target representative, use selected source validity of t and the
duplicate-endpoint result for its parent, H(t), H(a), the SAME fixed argument,
target representative y at t, and given C(d,e,y,a)=other. The frozen target
congruence contract yields the target parent representative at other.
Neither x=N(s) nor y=N(t) is assumed: the representative payload-transport
contract and the actual combine's payload dependence are the required bridge.

Reassemble selected parent-step acceptance and the two parent representative
graphs through the original encoded core-edge acceptance equation. For the
witness-free target, internally bind the three original certificate selectors,
the two raw application outputs and the step-lift output. Original edge
reconstruction and exact edgeLift commutation produce the graph of the SAME
supplied lifted certificate; use target 2. Do not change certificate numbering,
choose an alternate valid certificate, filter certificate zero, or omit any
malformed numeric input from the all-input calibration contracts.

## Paper correspondence and explicit exclusions

Paper 06 lines 537-549 define the subtype-closed source and function-side
auxiliary application rule; lines 551-556 define least-code representatives
and the arithmetic quotient edge; lines 558-560 state the larger accessibility
lemma. This packet is precisely a local core-edge compatibility component.

Vertex/full-context dispatch, output typed-invariant exposure, the OUTER typed
edge wrapper, generic path assembly, context-uniform selection, malformed outer
pathValue treatment, the full CertifiedApplicationLift premise, multiset/
constructor/lambda/substitution and all-term accessibility remain outside this
target. No numbered theorem is promoted. No full-root build, remote CI or Git
publication is claimed.

## Freeze and validation boundary

This packet contains Definitions, Targets, comparator-only Preflight and exact
source/correspondence pins. Independent review and serialized bounded native
preflight must pass before any proof authoring. No compiler was invoked or slot
requested by the freezing worker. The selected-guard and representative-
congruence supplier contracts are frozen, with candidate proofs being handled
separately; they must pass their own exact gates before final acceptance here.

Later native work must use `scripts/check.py` with a fresh sole-slot grant,
2048 MiB heap, 1536 MiB RSS, 2048 MiB minimum-free, one thread, 90-second CPU
and 180-second wall caps, and pinned upstream cache only. Actual axiom closure
must be confined to `propext`, `Classical.choice` and `Quot.sound`.
