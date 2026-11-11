# Original source neutral applications: source correspondence

**Status: all seven exact supporting contracts accepted.** This continuation
extends `cbda2bacd4fce5de5ca6ae7976a7b2426a5fb553`.
[ACCEPTANCE.json](ACCEPTANCE.json) records the source-matched native, exact-type
and standard-axiom evidence. All fourteen frozen specification/preflight files
retain their reviewed hashes. These contracts support paper06 `lem:id1`;
the lemma and numbered register remain unchanged.

## Source relation and the first-edge boundary

The source is [paper06](../../../../06-godel-t-termination-ordering/paper.tex),
whose inherited SHA-256 is
`bdafe9f113ec4e3ffc390a5a744ae6337f197ab9a69ddcecd006d5dc08c4a66e`.
The least-code quotient defines the one-step relation `H` and accessibility
relation `R = H^+` at lines 551–556. The non-lambda application case at lines
578–584 uses function-side reduction and reduction to bottom. Auxiliary
application has no argument-side monotonicity rule.

The scalar source certificate is the literal
`InternalAccessibilityRules.certificate src false`. Its `false` selector
chooses `src.positive`, so it is an accepted positive-path certificate, not
an assertion that its endpoints form a single quotient edge. After exposing
the original Object coordinates, its raw relation is
`InternalParameterizedPathChecker.positiveGraph
  (UniformCertificateCompletion.edgeChecker data oldStep)`.

The checked path consumer therefore classifies only the **first edge** of
that positive path. The first entry is the original list cons containing the
original encoded pair of its vertex and certificate. Its tail is an ordinary
`pathGraph`, which permits the empty path and retains the caller's exact final
endpoint. A function reduct may be a lambda; a subsequent beta step may change
the endpoint's constructor shape. Neither the one-edge rule nor its path
wrapper claims that the final positive-path endpoint is an application or a
bottom, or that the recovered function remains a non-lambda.

## Accepted supporting contracts

Seven contracts are frozen across fourteen specification/preflight files:
four rule groups and one global packaging contract. Each rule group has its
own definitions, exact targets and preflight module in
`LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/SourceComputabilityCompletion/`.
The global selection has its own frozen target and preflight. The frozen
manifest is authoritative for every exact source hash; all seven exact contracts passed native and standard-axiom acceptance.

| Exact contract | Original premises and proved result |
| --- | --- |
| `ActualOriginalNonLambdaApplicationNeutrality` | Original typed application inputs, the supplied actualJ graph and the requested function's original non-lambda tag yield neutrality of that actual application output. |
| `ActualOriginalNonLambdaApplicationEdgeElimination` | The same original inputs and an accepted quotient edge yield same-codomain bottom or the inherited aligned function-child edge record, without a separate canonical-neutrality premise. |
| `ActualOriginalPositivePathFirstStepElimination` | An accepted original positive path internally supplies its first list entry, paired vertex/certificate, accepted first edge and exact ordinary suffix. |
| `ActualOriginalNonLambdaApplicationPositivePathElimination` | An original non-lambda application and positive path give the bottom/function split at that first vertex while retaining the complete suffix. |
| `ActualOriginalSourceNeutralApplicationInputs` | The original Object application domain and accepted output internally supply a common runtime Gamma, raw inputs/output, symbolic parameter, original application premises and the non-lambda observer equivalence. |
| `ActualOriginalSourceNeutralApplicationPositivePathElimination` | The original Object domain, accepted application, Object non-lambda premise and positive source certificate internally supply those coordinates and a classified first raw edge, preserving the requested Object endpoint and suffix. |
| `ActualOriginalSourceNeutralApplicationGlobalSelection` | One globally calibrated original tuple retains the complete package and every predecessor law, adding the original non-lambda edge/path rules and the Object-input/source-positive-path rules for all finite source windows. |

All specialized contracts use the same
`OriginalApplicationSidecar.finalInputs p` tuple as the accepted predecessor.
The generic first-entry decomposition applies to arbitrary original `data`
and `oldStep`; it changes no selected Program.

## One globally calibrated tuple

The global contract selects one `GlobalSourcePackage.Inputs` tuple before
every finite source context and runtime Gamma. Its same `finalInputs` tuple
retains both the input calibration and complete `GlobalSourcePackage.Package`,
including the original source, computability and application-lift Programs.
It retains root-field reflection, function-neutrality preservation, the
neutral-bottom law, paired canonical components, generic neutral quotient
inversion, requested-argument application-edge inversion, and both variable
Object laws.

The new non-lambda one-edge and positive-path laws hold for that same data,
window and old step checker. The Object-input and source-positive-path laws
hold at every original subtype-closed context code, with runtime Gamma still
bound internally. This package does not contain the finite-type computability
induction or the closed all-term accessibility conclusion.

## Non-lambda premise and actualJ

`OriginalNonLambdaApplication.nonLambda function` negates the graph of the
original constructor-tag observer at the lambda tag `1`. It introduces no
replacement source checker. The source/Object observer composes that same
tag Program with `InternalUnpair.right`; it reads the raw function payload
of the original Object and is not installed in the source or computability
tuple.

The accepted predecessor identifies the original actualJ output with the
whole-child application constructor at the **requested function** and the
actual full-fold output of the requested raw argument. Its proof obtains
transition fixedness from selected typing and then derives sidecar fixedness.
It neither assumes nor proves full-fold fixedness of the requested function.
That equation supplies the constructor needed to derive the new output
neutrality from the original non-lambda tag. The raw argument is retained
literally in the aligned target actualJ graph.

The one-edge rule then consumes the already accepted
`OriginalNeutralApplicationEdge.Recovered` contract. Its function case retains
all raw quotient witnesses, original accepted function-child step, same-checker
function-child quotient edge, target-function typing, canonical argument and
the target's actualJ graph at the requested raw argument. These facts remain
internally derived conclusions; the new caller does not provide them.

## Object application inputs

`OriginalSourceNeutralApplication.ApplicationInputs` takes only the original
`InternalComputabilityDownward.domain` and
`InternalComputabilityApplication.accepted` formulas. The supplied output
Object is arbitrary; it is not given a pair shape in advance. The recovered
record retains both premises and exposes literal original pairing graphs for
the function, argument and output Objects at one common runtime Gamma, plus
the parameter pairing of the fixed source context with that same Gamma.

The full `InternalOriginalUniformApplicationTyping.applicationPremises`
supplies the original arrow constructor, codomain membership, selected typing
of both raw inputs and the unchanged actualJ graph. Its weaker
`OriginalNeutralApplication.InputPremises` records the window activation,
selected function typing and argument validity/type facts needed by the
accepted application equation. The source's calibrated window and
subtype-closed membership machinery discharge those facts internally.
No window, raw coordinate, member fact, canonical output, or canonical
neutrality is added to the Object caller's assumptions.

The recovered non-lambda equivalence transports the Object observer premise
to its raw payload. The input-exposure theorem itself assumes neither side
of that equivalence. It is formulated for an arbitrary fixed positive body;
the source path consumer specializes it to the original
`SourcePresentation.sourceBody src context`.

## Original positive source certificate

The source path consumer keeps the original domain, accepted application,
Object non-lambda premise and source certificate in `PathInputs`. It derives
the raw non-lambda premise and retains a target-Object pairing with the same
runtime Gamma. All source and target coordinates, the symbolic parameter and
the path's first-entry witnesses are bound internally through continuation
elimination.

The correspondence uses existing exact source helpers:

1. `OuterGammaProof.targetGamma` derives the target Object's shared Gamma
   from the original positive certificate.
2. `OuterPositiveRawProof.rawPositiveRecover` recovers the actual raw positive
   checker at the unchanged source payload, target payload, witness and
   parameter. The original calibrated window supplies its active branch.
3. `OriginalVariableObjectSupportProof.positiveRecover` removes the wrapper guards and retains the same positive path graph.
4. The new first-entry rule exposes one accepted quotient edge and its exact
   ordinary suffix. The new non-lambda edge rule classifies that edge alone.

`RecoveredPrefix` conjoins those complete source inputs with the exact
`FirstStep` record. The bottom continuation receives the first vertex's
literal bottom graph at the requested codomain. The function continuation
receives the inherited aligned edge record for the source payload and that
first vertex, including the requested raw argument. Both continuations keep
the original final endpoint in the suffix and retain the original source
calculus under every context embedding and term renaming.

## Preservation and remaining theorem

Acceptance verifies inherited sources and preceding checkpoint evidence against
the `cbda2bacd` pin manifest, all frozen specification hashes, and exact types
and axiom dependencies against successful source-matching native logs. The
checker, dependency/toolchain pins, manuscripts and serialized profile remain
unchanged.

The packet discharges the original non-lambda-to-canonical-neutrality bridge
and Object input/common-Gamma/symbolic-parameter exposure, including internally
derived window activation and membership. The original source H+ wrapper
classifies the first raw vertex and retains the exact ordinary suffix to the
requested endpoint.

The next computability consumer still needs the original function-child Object
certificate and original accepted Object application at that first vertex.
The same-checker raw child edge, target-function typing and aligned actualJ
graph are already available. The finite-type neutral/arrow induction remains
separate, followed by lambda/substitution, multiset and numbered-constructor
closure, and the closed all-term endpoint.

Paper06 `lem:id1` remains pending; the register is 171 checked, 2 inherited and
16 pending out of 189. [NEXT-STEPS.md](NEXT-STEPS.md) records the next consumer.
