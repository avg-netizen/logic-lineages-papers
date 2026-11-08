# Original application step: validation and consumer API

The two exact frozen propositions are proved. The public proof module is
`InternalOriginalApplicationStepProof`, exporting:

- `actualOriginalGuardedApplicationStep`
- `actualOriginalSelectedApplicationStep`

The two statement-check aliases have exactly the preflight comparator types.
Their actual axiom closures and all seven supporting/exported proof entries
are contained in `propext`, `Classical.choice` and `Quot.sound`.

## Exact selected checker

The selected data has only old validity, unary membership and ternary old-step
Program leaves. The constructed validity is literally the existing
`recursiveData`; the structural endpoint uses that same validity and member;
the normalized core uses that endpoint and old step; and the original outer
guard wraps that same core. No correctness or derivability field is stored.

For each fixed signature, original symbols, arbitrary S, Gamma and table,
the existence proof selects these leaves once, before all internal bodies,
variable types and symbolic terms. It composes the checked recursive validity,
endpoint, normalized-step and outer-guard calibrations to preserve the entire
original functions on all natural inputs. This includes malformed sources,
packed targets and certificates, unequal raw types and arbitrary windows.
None of these external equalities is reflected into symbolic graph proofs.

## Internal proof and exact premises

The premises are the actual arrow cons graph, selected structural endpoint
acceptance, two original raw application graphs, original stepLift graph, and
acceptance of the original step by the selected guarded checker. In particular,
no new validity or acceptance at the lifted terms is a premise.

The endpoint factorization supplies all child tag graphs. Conjunction
elimination exposes the original normalized-core output-one graph. The
checked `checkerBackward` transports it along the original application and
certificate graphs. The checked
`actualOriginalRecursiveEndpointApplicationValidity` supplies source and
target validity of the two applications from the exact endpoint premises.

Two new small helper proofs derive outer codomain tags from the original
application AST. Composition elimination exposes its actual pair node;
projection functionality fixes the codomain; the original pair inverse
gives the tag. All intermediate witnesses are discharged internally, and
these tag helpers hold even on malformed child codes. The outer guard is
then reconstructed using the newly proved validities, both codomain tags,
reflexive type equality and the transported core acceptance.

This proves accepted-step transport in the original calculus for arbitrary
positive bodies, variable types, actual leaf ASTs and symbolic inputs. The
target is the minimal forward output-one rule, not a new full-output
equivalence claim for arbitrary guarded wrappers.

## Reusable contextual helpers

`InternalOriginalApplicationStepSupportProof.applicationStep` works in an
arbitrary internal formula context Gamma. Its arguments are data, arrow,
domain, codomain, source, target, argument, original certificate, source
application, target application and lifted certificate, followed by
derivations of liftPremises and original accepted step.

`applicationTag` takes domain, codomain, function, argument and output plus
the original raw application graph, and derives its actual unpair-left tag
at the supplied codomain. `packedApplicationTag` supplies the analogous rule
for arbitrary four-coordinate input tuples.

`InternalOriginalApplicationStepEvaluationProof.selectedCalibration`
provides the all-input calibration of the exact wrappers from calibrated
leaves. `calibratedDataExists` selects those original leaves.

The old `InternalTypedEdgePresentation` existential alone is not used: it does
not force recursive validity. Future typed integration must explicitly
construct its data with this same recursive validity and reuse parameterized
presentation/calibration helpers. Representative application congruence is
a separate remaining obligation.

## Evidence and reproduction

Independent static review accepted both frozen targets before native
preflight. The three specification modules compiled before proof authorship.
The second candidate passed the exact gate and all namespace audits. The
first candidate, logs and immutable failed receipt remain local; its repairs
only supplied explicit vector arguments for projectionValue and corrected
the closedApply namespace. No statement, definition or premise changed.

The local import closure of preflight and exact gate has 1,160 source-matched
modules, including meta imports. Each current hash matches a successful
native receipt; existing matching supplier receipts are reused. There is no
claim of a fresh whole-closure or full-root build. All 42 frozen specification,
correspondence, original prerequisite and paper comparisons passed unchanged.

The unchanged profile is one thread, heap 2048 MiB, RSS 1536 MiB, at least
2048 MiB free memory, CPU 90 seconds and wall 180 seconds, using pinned cached
upstream dependencies only. Peak successful component process-tree RSS is
1,057,100 KiB; inherited closure receipts have maximum RSS 1,176,760 KiB.
The toolchain is Lean v4.32.0-rc1.

Reproduce the exact gate from formalization with the existing toolchain:

    python3 scripts/check.py --memory-mib 2048 --rss-mib 1536 --min-free-mib 2048 --threads 1 --cpu-seconds 90 --timeout 180 LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalApplicationStepStatementChecks

The portable packet contains the seven accepted source modules, immutable
source freeze, correspondence, current closure pins and concise acceptance,
status and API evidence. Detailed receipts, logs, failed snapshots and
compiler-slot evidence remain local. No Git action was taken.

This does not prove representative congruence, the complete typed-edge/path
assembly, joint-context uniformity, outer pathValue handling,
CertifiedApplicationLift, source constructor/lambda/substitution/fundamental
rules or all-term accessibility. No numbered source statement is promoted.
