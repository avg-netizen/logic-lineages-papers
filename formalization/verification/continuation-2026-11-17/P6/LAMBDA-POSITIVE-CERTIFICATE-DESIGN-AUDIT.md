# Lambda positive-certificate design and obstruction audit

2026-11-17, read-only; no target frozen, proof edited, compiler run or new
counterexample theorem claimed. Paths relative to
`LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/` unless
prefixed `../`. This supplements NEXT-CLOSED-ALL-TERMS-OBLIGATION.md.

## Decision in brief

For the ORIGINAL calibrated typed relation, lambda to nonbottom along a positive
path should remain lambda and project to a positive body path. This is a
source-level mathematical deduction from already proved native shape/primary/
bottom-terminal suppliers, not an internal Derivation obtained by calibration.
The known local stability discrepancy is not used or repaired by that argument.

For arbitrary input Programs at the unchanged sidecar/spine tuple, the blanket
internal analogue is not supplied by the existing guards: its oldStep has no
lambda-child guard. At the prepared traversal tuple the hereditary guard DOES
supply same-leaf child acceptance, but that alone still does NOT supply the
normalized selected child checker used by quotient edges. This distinction
blocks the naive one-hop proof before any path induction.

## 1. Literal positive path and one-hop APIs

For either selected final tuple r, set data=OuterSelection.data r.base r.window.
The literal source path chain is:

* `UniformCertificateCompletion/OuterDefinitions.positive` branches on window,
  retaining oldSrc.positive when inactive; active `positiveBranch` pays
  same-Gamma and calls `rawPositive data r.oldStep bottom measure` at the raw
  packed endpoints, original path certificate, and pair(context,Gamma).
* `rawPositive` = `PositiveGuard.checker bottom measure (edgeChecker data leaf)`.
  The checker is nonBottomGuard AND spineGuard AND
  `InternalParameterizedPathChecker.checker edge true`. The guards are on the
  WHOLE endpoints, not silently on every suffix.
* `InternalParameterizedPathCheckerDefinitions`: list entries are literal
  pair(vertex,edgeCertificate); summary is `listRec` carrying [target,parameter].
  `finish true` rejects nil; `finish false` accepts nil exactly at equal endpoints.
  A cons checks one edge and a REFLEXIVE suffix at the SAME parameter.
* `InternalParameterizedPathCheckerTargets` / Proof provide actual nil and cons
  arithmetic iff laws. `SCC/OriginalNonLambdaApplicationPathFirstStepProof.
  actualOriginalPositivePathFirstStepElimination` already binds exact raw/tail/
  vertex/certificate witnesses from positive acceptance for ANY data and leaf.
  Its `FirstStep` predicate retains both original code equations and suffix.
  Do not count this existing generic path decomposition again.
* `UniformCertificateCompletion/SupportProof.checkerRecover` and
  `actualParameterizedQuotientEdgeFactorization` expose a single edge certificate
  via actual selectors s,t,k:

      stepAccepted data leaf s t k parameter
      AND sourceRepresentative(data)(s)=x
      AND targetRepresentative(data)(t)=y.

  sourceRepresentative is validity-filtered foldN; targetRepresentative is
  unfiltered foldN. These are RAW representative witnesses, not x/y themselves.
* `stepChecker` (UniformCertificateCompletion/Definitions) conjoins raw source
  validity, raw target target-validity, equal outer type, selectedChecker, and
  target source-validity. `OriginalSelectedStepInverseTargets` splits the ACTUAL
  selectedChecker into an unpeeled leaf or accepted application-child selected
  checker, preserving guards. This is application peeling, not lambda descent.

## 2. Why the native lambda path shape is credible

Already proved native APIs (outside ID1Completion):

* `NumberedLambdaRootProof.actualLambdaStepCases`: an original WindowStep out
  of lam body is same-type bottom or lam body' with an actual body WindowStep.
* `NumberedPrimaryLambdaBodyProof.actualPrimaryLambdaBody`: primary-equivalent
  lambdas correspond exactly to primary-equivalent bodies at sigma::Gamma.
* `NumberedBottomAccessibilityProof.actualBottomPrimaryRigid`,
  `actualBottomStepTerminal`, `actualBottomPositiveTerminal` prevent a bottom
  visit followed by another original quotient hop.
* `NumberedLeastCodeRepresentative` representative equality and confinement,
  and `SCC/OriginalLambdaCanonicalTargets.ActualOriginalLambdaRepresentativeFactorization`
  provides the literal canonical coding bridge.

A one-hop quotient lambda case follows by opening its raw representatives,
using primary lambda-body correspondence, inverting the raw WindowStep, and
reassembling the child quotient edge. If its target is bottom, no further hop
is possible. Thus a path with nonbottom endpoint never takes that case; every
remaining edge is a body edge at the same extended Gamma, and list induction
projects a positive path of the same nonzero length. No substitution-stability
axiom is needed. This paragraph is a mathematical route, not a newly checked
Lean theorem, exact certificate transformer, or permission to reflect native
semantic truth into the object calculus.

## 3. Unchanged sidecar/spine versus prepared traversal

Unchanged:

    r0 = OriginalApplicationSidecar.finalInputs
           (OriginalSpineGuardLeaf.refineInputs q).

Its leaf contains spine, neutral-application and constructor guards. Inspection
of `OriginalNeutralLeafDefinitions.neutralTest` confirms it triggers only at
an APPLICATION with nonlambda function. `OriginalConstructorLeaf` governs
bottom/variable sources; the spine guard governs bottom-spine sources. These
are not lambda-child preservation clauses. A theorem universally quantified
over arbitrary q cannot infer original numeric lambda semantics from these
wrappers. A calibrated q has the right native semantics, but calibration is
not an arithmetic derivation supplier.

Prepared:

    rT = OriginalLambdaTraversalSelection.finalInputs q
       = OriginalHereditaryLambdaGlobal.finalInputs
           (OriginalLambdaTraversalSelection.prepareInputs q).

Here literal identities give the actual `closedLeaf` and same-final validity/
canonical laws. `OriginalHereditaryLambdaGlobalProof.finalChildElimination`
instantiated at prepareInputs q recovers matching lambdas, original lam-prefix
certificate, exact source/target child selectors, the cons-extended parameter,
and acceptance by rT.oldStep at those child inputs. Existing
`FinalBodyFixedLaw`/`FinalLambdaEquation` handle the same-final canonical bodies.
These are genuine reusable suppliers, but the next point is still unpaid.

## 4. Concrete obstruction: leaf acceptance is not normalized child acceptance

`InternalOriginalUniformApplicationStepSelection.selectedChecker data leaf`
is `checkerP (selectedEndpoint data) leaf`, not leaf. Its exact definition in
`InternalParameterizedApplicationStepCheckerDefinitions` is:

    repeat the application-peeling transition along the original path;
    call leaf on the selectors of the resulting normalized state.

A parent whose source tag is lambda cannot take an application-peeling step.
After hereditary lambda elimination, however, its body can be an APPLICATION.
The recovered child leaf acceptance is at the UNPEELED body tuple. The child
selectedChecker may peel that application and invoke the SAME leaf at a
DIFFERENT tuple. No generic graph implication connects these two leaf calls.

Counterexample mechanism to the unrestricted GENERIC leaf-to-checker lemma:
choose a genuine lifted application/certificate tuple with accepted endpoint
and a distinct peeled tuple; choose a primitive-recursive leaf that accepts
the unpeeled tuple and rejects the peeled tuple (finite tuple equality tests
suffice). The exact lifted-checker iff forces selectedChecker at the lifted
input to use the peeled rejection, even though leaf at the lifted input is one.
One can also let the leaf accept a parent lambda tuple whose hereditary scan
stops at this application child. Hereditary child acceptance then remains true
without repairing the normalized child check. This is an explicit source-level
counterexample DESIGN to a generic lemma, not a newly compiled numeric witness
or a claimed counterexample to the calibrated original source relation.

The missing unrestricted internal supplier is therefore a concrete original
leaf acceptance -> actual selectedChecker acceptance theorem on the relevant
valid child configurations, or a stronger prefix/normalization compatibility
proved from the actual original leaf AST. It must be derived, not put in a
public target as a new "normalization agrees" oracle. Existing
`ActualParameterizedOriginalCheckerCalibration` is native and does not pay it.

## 5. Smallest honest bounded support statement

Before attempting quotient/source paths, a useful restricted target can be
specified at rT without an oracle:

Given actual rT.oldStep parent acceptance, literal LambdaNonbottom tests, and
an actual graph showing the extracted child's source tag is NOT application
(tag two), internally bind the SAME ChildRecovered witnesses and additionally
derive `graph4 (selectedChecker (finalData q) rT.oldStep) 1
sourceChild targetChild childCert childParam`.

The nonapplication test must be on the actual sourceBody selector (or its
internally linked witness), not an arbitrary child. State it as a genuine tag
observation/negative formula, not as supplied guard rejection or normalized
acceptance. Its route is hereditary elimination, source-tag mismatch implies
structuralGuard=0, exact transition identity, original list-recursion fixed
iteration, then composition with the recovered same leaf graph. It preserves
all certificate and parameter coordinates. It is deliberately only a
nonapplication-child support result: it does NOT establish full lambda
computability or silently restrict ContextUniformTargets.

For the unrestricted next target, freeze FIRST a lambda quotient ONE-HOP
elimination with two continuations: same-type bottom, or actual canonical
lambda-body quotient edge at the extended parameter. Retain the original raw
edge selector witnesses and show all selectedChecker/validity/canonical child
facts as conclusions. The application-child compatibility in (4) must be paid
before this target can honestly be proved for arbitrary prepared inputs.
Only after that should an exact positive-path body transformer be introduced.

## 6. Important side conditions for a future full source path result

* At unchanged r0, a valid-window observation is necessary to enter the actual
  branch; otherwise the entire opaque oldSrc.positive fallback remains.
* At the raw path level keep source/target LambdaFields and actual type/domain/
  context extension. Equal native contexts cannot rewrite internal graphs.
* A final nonbottom endpoint excludes an earlier bottom only AFTER same-final
  quotient bottom-terminal has been proved. The outer nonBottomGuard alone
  checks only the first endpoint and cannot justify that inference.
* Body certificate construction must rebuild quotient triples and path entries,
  not merely apply stripCertificate to the OUTER positive list. stripCertificate
  strips a position in an INNER StepCertificate; these are different encodings.
* To return a certificate of src, pay the child Object same-Gamma/typing,
  whole-path nonbottom/spine guard and active-window conditions. The child
  parameter uses cons(domain,Gamma), but the outer context stays unchanged.
* Preserve the immutable local-stability discrepancy. The shape argument does
  not imply arbitrary substitution stability or repair any counterexample.

No counterexample to calibrated lambda-to-nonbottom path shape was found in
this audit. The demonstrated limitation is the unjustified generic internal
bridge, not a refutation of the typed mathematical fact.

## 7. Is today's original leaf internally inspectable?

The chosen global leaf is currently existential, not a new explicit raw-step
AST with an internal constructor theorem. Exact selection chain:

* `UniformCertificateCompletion/GlobalSourcePackageProof.
  actualOriginalGlobalInputSelection` obtains oldStep from
  `InternalOriginalUniformApplicationStepSelectionProof.
  actualOriginalUniformStepLeafProgram`.
* The latter forwards to `InternalOriginalUniformApplicationStepSelectionEvaluationProof`.
  Its proof literally invokes `Proof.allPrimitiveFunctions 4 _
  (leafValuePrimitive n arity)` and retains the resulting evaluation calibration
  and calibrated parameter slices. No internal lambda/application-normalization
  compatibility theorem accompanies that existential witness.
* The semantic `leafValue` decodes original context/Object and evaluates original
  numericStepTest. Its mathematical meaning is not in doubt; what is missing
  is an internal graph theorem for the selected Program at symbolic inputs.
* Today's `Membership.inputs` installs an explicit primary class/minimum into
  base.oldRepresentative through `OriginalTransparentMinimum.minimumInputs`.
  It does not replace oldStep. Rank-guard/transparent-input literal fields also
  retain oldStep. Concrete initial installation therefore exposes a new
  representative, not a new internally transparent original step verifier.
* Sidecar/hereditary/traversal wrappers are explicit, inspectable ASTs, but
  their surviving oldStep call is still this existential leaf. The wrappers'
  proved graph laws only expose the factors they actually check.

Consequently an unrestricted body application-normalization compatibility proof
cannot be obtained merely by unfolding today's concrete primary installation.
A legitimate continuation must expose/derive the required actual leaf graph
contract (possibly by a separately calibrated explicit original numeric-step
implementation) and integrate it while retaining the exact source semantics,
or supply another honest internal derivation avoiding this bridge. Adding the
compatibility contract as a field of Inputs or a premise of closed accessibility
would not pay it. The arbitrary-leaf obstruction is diagnostic; it is NOT a
counterexample to the selected calibrated original leaf's native behavior.

### Final bounded-task recommendation

Do NOT implement or count the restricted nonapplication-child helper in (5)
as progress on the required all-child contract. It leaves precisely the hard
application-child case unpaid. Preserve this design note instead. The next
honest development should freeze the ALL-child normalization/selected-checker
contract at an internally exposed original leaf, with concrete source supplier
and native/internal responsibilities separated. No such supplier was found in
the inspected current selection chain; that is the precise blocker to a safe
new full lambda/source certificate target in this pass.
