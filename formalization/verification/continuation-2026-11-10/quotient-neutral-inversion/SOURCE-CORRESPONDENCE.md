# Original quotient-neutral inversion: source correspondence

**Status: all seven exact contracts accepted.** The source-matched native,
exact-type and standard-axiom evidence is recorded in [ACCEPTANCE.json](ACCEPTANCE.json).
This supporting packet does not complete a numbered source statement.

## Paper and original relation

The source is [paper06](../../../../06-godel-t-termination-ordering/paper.tex),
whose SHA-256 is
`bdafe9f113ec4e3ffc390a5a744ae6337f197ab9a69ddcecd006d5dc08c4a66e`.
The relevant passages are the original least-code quotient and definition of
`H` and `R = H^+` at lines 551–556, and the non-lambda application case of
`lem:id1` at lines 578–584. Auxiliary application has function-side reduction
and bottom reduction; it has no argument-side monotonicity rule.

The numerical relation remains the literal
`UniformCertificateCompletion.edgeChecker data oldStep`. Its raw
`stepChecker` includes source validity, target admissibility, equal outer
types, the original selected step checker, and the additional retained target
source-validity check. Its quotient factorization is exactly:

1. the accepted original raw step;
2. the filtered source-representative graph at the raw source;
3. the unfiltered actual canonical-fold graph at the raw target.

`SupportProof.checkerRecover` and `SupportProof.checkerAccept` are the matching
factorization and reconstruction rules. The similarly named normalized-core
checker has different requirements and is not the relation in these targets.

## Frozen contracts

Seven exact contracts are frozen across eleven specification/preflight files:
the raw-step quotient supplier, neutral quotient inversion and its global
selection, and the original typed application equation and internal
eliminator, followed by requested-argument neutral application-edge inversion
and its global selection. All seven passed native exact-type and standard-axiom acceptance.

The following files are in
`LogicLineages/OrdinalComparison/TerminationOrdering/ID1Completion/SourceComputabilityCompletion/`.

| File | SHA-256 |
| --- | --- |
| `OriginalUniformStepQuotientTargets.lean` | `cf8de8ef674d6231b7182aced0d15b38d9bed68837d945476d6b3d3d78787cc4` |
| `OriginalNeutralQuotientDefinitions.lean` | `c96be93364c197bb5805727524faca7ca24077c23611548e863be2cf3351c36b` |
| `OriginalNeutralQuotientTargets.lean` | `2450514d15f30c83354c7cf526f85d1e792f01711d00bfc4158927e62153e7a9` |
| `OriginalNeutralApplicationDefinitions.lean` | `2ef1aa38dd7e0d733fce6462151bcd101a177c82d10b0892d0b6511eeed5b8b0` |
| `OriginalNeutralApplicationTargets.lean` | `bb7c1712bab7b9e23d45e1e853b4f32d1d1a67e5605d2a383c5360af6e52a944` |

The aligned `OriginalNeutralApplicationEdgeDefinitions.lean` and
`OriginalNeutralApplicationEdgeTargets.lean` and the matching four
`Preflight.lean` modules are also frozen in `FROZEN-SPECS.json`. These hashes
identify the unchanged statements; the separate native records establish acceptance.

### Accepted raw step to the original quotient edge

`ActualOriginalUniformStepQuotientElimination` starts with only an accepted
original raw step. Both endpoint validities are recoverable from that actual
checker. Totality of the original Programs binds the two actual canonical
outputs and the `edgeCode` certificate internally. The recovered record
retains the original raw endpoints, raw step certificate, symbolic parameter,
both validities, both fold graphs and acceptance by the SAME quotient checker.

The caller supplies no output witness, canonical-fold graph, filtered-source
graph, target graph or calibration premise. The continuation transports every
original input through its explicit renaming. This is a supporting internal
reconstruction theorem, not a replacement quotient definition.

### Neutral quotient-edge elimination

`ActualOriginalNeutralQuotientEdgeElimination` specializes to the SAME final
sidecar-refined tuple as the inherited global package. Its entry assumptions
are the active original window, the actual accepted quotient edge, neutrality
of its source endpoint and that endpoint's literal outer type field. It
internally recovers all raw certificate fields, application constructors,
peeled-step witnesses and actual canonical child outputs.

The bottom continuation receives the literal same-type bottom graph for the
target endpoint. The other continuation receives the original selectors and
checker requirements, the original accepted peeled function-child step, the
child's original `edgeCode` and SAME-checker quotient acceptance, and one
actual canonical argument shared by both canonical application constructors.
The raw argument is retained and folded once for this conclusion; it is never
identified with its canonical output.

The application equations use the checked final-leaf identity at the actual
canonical child outputs. Parent validity yields the child source/type facts.
The conclusion does not assume full-fold idempotence, equality of raw children,
a replacement semantics, or native reflection into the internal calculus.

### One global tuple

`ActualOriginalNeutralQuotientGlobalSelection` selects one original tuple
before every finite source window and ambient context. Its SAME final tuple
retains calibration, the complete `GlobalSourcePackage.Package`, root-field
reflection, function-neutrality preservation, the neutral-bottom law, paired
canonical-component coherence, and both original variable Object laws. The
new quotient-edge eliminator is an additional law of that same tuple.

No numbered statement is promoted by these supporting contracts. The
authoritative register remains 171 checked, 2 inherited and 16 pending out of
189; paper06 `lem:id1` remains pending.

### Original typed application equation and internal elimination

The source's arrow clause uses the supplied application operation
`InternalParameterizedCanonicalResultFold.actualJ`. This Program receives
the requested function directly and folds only its raw argument before one
`combine`. A source formula asserting `actualJ(q,u)=x` does not itself supply
`foldN(q)=q` or a second full-fold graph of an arbitrary raw application.

`ActualOriginalTypedApplicationEquation` specifies the original `actualJ`
graph iff the whole-child constructor graph `application(q,b)`, where `b`
is an actual canonical-fold output of the requested raw argument. Its
`InputPremises` retain the active window, original arrow constructor,
codomain membership, selected typed graph of the requested function, and
only raw source validity/type for the argument.

`ActualOriginalTypedApplicationElimination` removes the equation supplier's
externally given argument-fold graph by binding the actual argument output
internally. It retains both that fold graph and the original constructor
graph at the supplied `actualJ` output. The requested function and raw
argument remain literal under every continuation renaming.

The checked proof uses the selected function's actual transition
fixedness to derive sidecar fixedness, then combines it with derived sidecar
fixedness of the folded argument. This gives identity of the SAME final
leaf at the rebuilt application. Full-fold fixedness of the requested
function is neither a hypothesis nor a claimed conclusion.

### Requested-argument neutral application-edge inversion

The neutral quotient contract identifies the function child and canonical
argument actually recovered from the quotient witness. The checked typed application
equation and whole-child selector functionality align those with the requested
function `q` and the actual fold of the requested raw argument `u`.

`ActualOriginalNeutralApplicationEdgeElimination` establishes that separate
consumer. It uses the original typed input premises, supplied source `actualJ`
graph, canonical source neutrality and actual quotient edge. Its recovered
record retains the entire generic quotient inversion and application
decomposition, proves equality of the whole canonical components with the
requested function and requested argument's actual fold, and supplies the
SAME-checker function child edge, its target typed graph, and the target's
literal `actualJ` graph with the requested RAW argument unchanged.

All raw witnesses and the canonical argument output are bound internally.
The bottom continuation receives bottom at the requested codomain. Neither
component alignment nor a target application graph is a caller assumption.
`ActualOriginalNeutralApplicationEdgeGlobalSelection` retains the complete
calibrated package and all prior laws, including generic quotient inversion,
at the SAME final tuple while adding this aligned rule.

All seven contracts are checked. The subsequent source-level boundary is
recorded in [NEXT-STEPS.md](NEXT-STEPS.md).

## Boundary after the checked packet

The remaining obligations are source/path/Object wrappers, derivation of
canonical application neutrality from the original non-lambda function
premise, and finite-type neutral/arrow computability. Lambda/substitution,
multiset and numbered-constructor closure, and the closed all-term endpoint
`ContextUniformTargets.ActualContextUniformInternalAccessibility` also remain
pending. The one-step neutral split does not assert that later function
reducts remain non-lambdas.
