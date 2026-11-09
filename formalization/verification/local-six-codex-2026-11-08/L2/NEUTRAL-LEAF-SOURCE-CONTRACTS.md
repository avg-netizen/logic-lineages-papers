# Source contracts after the bottom-spine stage

This is a source-level design audit, not a checked internal theorem. Native
source proofs have been read; numerical calibration is not treated as an
internal inference rule. The same global source selection must satisfy every
contract below before the unqualified all-term endpoint can be claimed.

The native `SourceNeutralExpansionProof.actualNeutralComputabilityExpansion`
uses `NumberedNonLambdaPathsProof.actualNonLambdaApplicationPath` in its arrow
case. For a nonlambda function applied to a typed argument, every positive
successor is either the codomain bottom or is reached from a SAME-argument
application of a one-step function successor. This is strictly more than the
current local forward application edge lift. Its internal counterpart needs
certificate decomposition, not merely transport of an already supplied
function edge.

The native `SourceConditionalLambdaProof.lambdaInduction` uses the four-way
`NumberedBetaApplicationEdgeProof.actualBetaApplicationEdge`: codomain bottom;
substitution of primary-equivalent body/argument; application of arrow bottom;
or application of a lambda whose body has an edge under the extended Gamma.
The source body accessibility and substitution stability then supply the
computability of these outputs. None of those four inverse cases follows from
the current opaque oldStep calibration. Fresh-body accessibility and the
literal context extension also remain separate internal contracts.

The selected oldStep currently comes from
`InternalOriginalUniformApplicationStepSelectionEvaluationProof` via the
primitive compiler. The underlying original numeric checker is explicit:
`NumberedNumericStep.numericStepTest` decodes the original source universe,
packed target and `StepCertificate`; the latter is path + replacement + root
selector. `NumberedStepCertificate.stepTest` focuses the path, runs the root
selector in its actual hole Gamma, plugs the replacement and compares the
whole target. `checkerP` exposes app-function peeling around this opaque leaf.
It does not yet expose ordinary/numbered/lambda/root-selector inversions.

Smallest faithful next leaf work is a NEW globally calibrated oldStep
normalization that records only checks already forced by an accepted original
certificate: source root/tag, original path head and target constructor,
with the original fallback/rejection behavior on every malformed code. The
nonlambda application inverse case can then proceed by original path-list
induction, using existing app-function peel and literal root-case guards.
A guard must be shown redundant on ALL accepted original raw certificates;
existence of a semantic successor witness alone is not an executable extractor.
No final AST is frozen for this work and no assumed inverse-case fields have
been added to the calculus.

The representative side also needs explicit source shape facts beyond the
new full bottom-spine mark. Primary equivalence preserves isLambda and the
app-root decomposition natively. A full mark guard preserves flag/depth but
allows a nonspine flag-zero candidate of a different tag internally. A later
root-tag guard can pay lambda/nonlambda preservation. Equality of RAW app
children is NOT natively redundant: primary equivalence may change either
child. Application component correspondence must use canonical children or
certificate-supplied primary witnesses with their own checked algorithms;
requiring literal raw-child equality would silently change the source.

The native constructor/multiset argument and all-term substitution theorem
also require a concrete original calibrated `multiset` and `direct` choice.
L1 keeps those fields arbitrary inputs until final assembly, allowing L2 to
choose their internally transparent literal list/direct checkers without
combining clauses from incompatible existential source pairs.

The actual final `ContextUniformTargets.ActualContextUniformInternalAccessibility`
uses the closed `SourcePresentation.allTermsFormula`, universally quantified
in raw Object codes. A metalevel family of proofs for each concrete term is
therefore insufficient by itself. The final coded structural induction also
needs actual grammar/Gamma/type inversion from oldSource/oldTarget acceptance
at nonapp leaves. Current recursive V exposes app recursion and delegates the
other constructors to opaque leaves. A strategically shared prerequisite is
an all-input-calibrated refinement of those leaves by transparent original
source/target grammar validators: accept oldSource AND its redundant grammar
check, and similarly for target. Its literal graphs could supply constructor
fields, child source/target typing, binder-context extension and root-member
metadata without semantic calibration reflection. This is a proposed source
construction, not an assumed theorem or an opened extra proof stream.

A plausible finite-formula route to the universally coded fundamental theorem
uses the fixed local finite subtype-closed S: form a finite disjunction of the
actual C_tau formulas for tau in S, indexed by original type codes. Source
grammar inversion supplies the root type in S; subtype closure supplies its
arrow components, so coded-term induction can use one formula at this fixed
window, even though metalevel C_tau is recursive in arbitrary Ty. This is a
proof design only. It avoids incorrectly generalizing an infinite metalevel
per-type/per-term family to one closed universal derivation. Arbitrary encoded
Gamma and its binder extensions still need the genuine grammar/substitution
algorithms noted above.

The immediate typed-spine route also exposes the precise remaining C-to-I
bridge. In the arrow case, use a same-Gamma object whose payload is the
literal bottom of the domain type; typed-spine C supplies its computability,
the existing C application rule supplies codomain C, the type IH supplies
codomain I, and the checked relative inverse-application theorem returns I
for the original function. The domain bottom is typed only when its domain
type belongs to the local S. Do not assume that membership or reflect the
native rootType theorem into the object calculus. Recover it from the SAME
actual typed function graph, raw typed/member factors and the original
context-only membership slice. Since S and the domain type are fixed at this
metalevel step, the rejected membership branch can be closed by the existing
closed Program computation proof supplier; the accepted branch constructs
the symbolic-Gamma bottom using the checked BottomSource typing theorem and
literal outer typed/object-pair rules. No Gamma decode or fixed-fiber premise
is added. This is an unpaid assembly obligation after typed-spine I/C, not a
claim that the native computability-to-least proof has been internalized.
