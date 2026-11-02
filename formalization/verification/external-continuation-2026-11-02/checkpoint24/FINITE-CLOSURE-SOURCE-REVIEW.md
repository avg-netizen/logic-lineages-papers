# Accepted whole source review: paper06 finite closure

Public source mapping derived from the separate 05:30 UTC review supplement; accepted after independent validation and cumulative121. No frozen mathematical artifact or register is changed.

## Literal claim and domain

`06-godel-t-termination-ordering/paper.tex`, `lem:finiteclosure`, lines161–174: every recursively requested type belongs to the subtype closure K of the two ordinary input terms; every source head is an original-source head; every target observation and opening context belongs to the previously fixed finite family. Its proof also asserts generated free names lie in the original names plus opened ports.

The formal domain is arbitrary ranked signature `Symbol`, `arity`, arbitrary head precedence relation, arbitrary ambient typed context, and any two ordinary typed source terms, including different outer types. No well-foundedness, comparison success, normal form, or invariant premise is assumed at the root. K is precisely `inputTypes s t = typeSupport s ∪ typeSupport t`; names are actual input occurrence membership; B is `lambdaDepth t`. The original five mutually inductive comparison relations are unchanged.

## Exhaustive original recursive requests

`GuardedQueryGraph.Step` stores raw marked source AND raw marked target, and an explicit weak/strict mode. Its guards never require Frame, ordinary targets, recursive-premise truth, or finite-observation membership.

| Original clause | Actual requested child / supplier |
| --- | --- |
| Strict.mark | Exact successful partial `strictMark`, then weak request. |
| Var | No recursive request. |
| Abs | Both original bodies, same actually fresh typed port. |
| Fun | Actual equivalent-head/type guards, whole occurrence-list permutation, every candidate zip pair. `funPremisesCovered` extracts actual WeakMatch premises. |
| Put | Same head/base, mark at original output type with empty extras. |
| Select | Original selectable base-or-extra occurrence, exact suffix decomposition, full tuple of same-source selfcopies, actual Apply result if successful. Every unsuccessful attempt remains an `IssuedSelect`; no success is assumed for its execution theorem. |
| F-Abs | Literal `openMarked`, actual weakening of base/extras plus one fresh variable. |
| Copy | Every target argument, whole original marked source retyped to that argument type, original native/user head guard. |
| Stat | Same whole-source side requests; actual base/target occurrence permutations and nonempty removed partition; retained pair candidates and removed×inserted replacement candidates. `statPremisesCovered` extracts the real retained Weak premises and each actual chosen Strict replacement witness. Extras are not added to the Stat base multiset. |

Deterministic constructor coverage is the literal interface, not a separate deep result. Fun/Stat witness coverage is separately proved. The graph conservatively includes failed recursive matching candidates by omitting their truth premises, not by imposing the desired invariant. Matching helper lists only range over these explicitly preserved occurrence lists, so they introduce no additional term or type operation.

## Exact clause payment

1. **Every query source type and body-node type:** `stepPreservesFrame` proves actual `typesAllowed K`, operation by operation; `reachableFrame` starts with the actual ordinary input and inducts over any finite query path. `typesAllowed` checks outer/node/argument/binder types, not merely outer type. `FiniteQueryPrimitivesSupportProof.rootType` exposes outer type if desired.
2. **Retyped Copy/Stat requests:** target argument is decoded as an actual ordinary child; `targetChildObservation` proves finite observation membership. `observationType` derives requested type from `openedTypeSupport` and `actualResultSupport`. Thus no new type is admitted by a retyping premise.
3. **Select suffix/selfcopy/result types, including failure:** `everySelectAttemptClosure` establishes selected type, every supplied suffix type, result type, selected term and full selfcopy tuple bounds without success. `issuedSelectExecutionsBounded` applies the accepted exact `OriginalApplicationTrace.Execution` semantics to every real recursive Apply configuration. `PayloadBounds` checks remaining tuple types, current source/result types, substituted body/base/extras, actual append payloads, and any returned result. `evaluationEquation` links the trace to the original Apply implementation. Capture-avoiding substitution's internal structural type/head/name closure is supplied by the accepted structural substitution proofs, not a fabricated successful-result-only trace.
4. **Source heads:** Frame's `headsAllowed (fun h => h ∈ markedHeads (embed s))` and `literalHeadCalibration` mean literal membership in the original source head list. Marking, weakening, selfcopy, selection, substitution and append are paid by actual preservation proofs. Copy does not manufacture its target head in a source.
5. **Actual finite target observations:** Frame proves an existential ordinary body with raw target exactly `embed body`, plus membership in the fixed existing list `observations B t`. Ordinary-target status is a conclusion, not a transition guard. Plain-child closure and actual lambda opening preserve membership.
6. **Context validity and lambda budget:** `openedObservationMembership` converts that list membership into `ValidPorts (typeSupport t)`, a genuine located original subterm, typed injective port assignment and its opening. `openedDepthBudget` gives used ports plus actual remaining body depth at most B. `freshOpeningAvailability` proves an unused slot exists whenever the target is a lambda and that every such fresh opening is again in the list. The Step freshness guard therefore does not assume away a required opening. Existing `portContextEnumeration` establishes the literal finite family.
7. **Free names:** Frame's `Supported` combined with `supportCalibration` is actual marked free-occurrence membership, including base and extras and dropping lambda-bound variables. `liftAllowedList (inputNames s t) (portTypes P)` permits precisely the opened port binders and original free input names; each additional binder is True only at its own new variable. No ambient-context-wide all-allowed premise appears.

## Verification and source-review adoption

The prospective exact graph comparator preceded candidate proofs. All six original aliases, direct successful main/frame/support sources, unchanged closure and permitted axioms were independently verified, followed by cumulative121. Those aliases are unchanged in cumulative125. The full source mapping above was reviewed against manuscript lines161–174 and accepted after those checks. Original proof files and frozen correspondence were not edited for this review.

Together with accepted FiniteQueryPrimitives, OriginalApplicationTrace and existing finite-observation suppliers, this pays the literal finiteclosure claim for generated recursive requests and actual Select primitive execution states. The earlier checkpoint23 summary prudently withheld the whole label before this source review. The full source claim is now completed but unregistered; TARGETS publication remains separately permission-gated.

Not claimed: a generated source-syntax size bound, finite-domain semantics, termination/completeness or adequacy of a decision procedure, strong-pair theorem, or source ordinal realization.
