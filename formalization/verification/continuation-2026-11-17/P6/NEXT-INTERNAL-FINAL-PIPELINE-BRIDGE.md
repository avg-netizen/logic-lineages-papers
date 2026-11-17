# Next internal bridge after initial representative coherence

Read-only audit, 2026-11-17. No compiler, theorem, frozen-target or count change. Names are relative to ID1Completion / SourceComputabilityCompletion (SCC). This is not a claim that final-pipeline coherence has been proved.

## 1. Fix two different objects: final Inputs versus selected Data

Let q be exactly the accepted initial tuple:
`OriginalRankGuardedRepresentative.transparentInputs H G W (Membership.inputs p H G L D)`
with today's concrete H/G/Q/E/L/D. Put b = OriginalSpineGuardLeaf.refineInputs q, r = OriginalApplicationSidecar.finalInputs b, and S1 = OuterSelection.data r.base r.window. The current theorem concerns q.base.oldRepresentative. It does not concern r.base.oldRepresentative, S1.oldRepresentative, the selected bounded-descent representative, or the full canonical fold. These four levels must not be conflated.

Literal field chain from source definitions:

* q.base.oldSource = OriginalUniverseDecoder.source H G (InternalOriginalUniformContextMembership.contextMember p.base.member) W.
* q.base.oldTarget = OriginalTypedDecoder.target H G; q.base.member = p.base.member; q.window = p.window. These follow from original transparent/rankguard/minimum record construction, not calibration.
* OriginalSpineGuardLeaf.refineInputs changes ONLY oldStep, by an actual conjunction with its spine guard. b.base=q.base and b.window=q.window.
* OriginalApplicationSidecar.refineInputs changes ONLY base.oldRepresentative to its branched sidecar representative. It does not change source/target/member/window.
* OriginalFunctionNeutrality.refineInputs then changes ONLY oldRepresentative by its neutral-mark fallback.
* OriginalConstructorShape.refineInputs changes ONLY oldRepresentative by its constructor-tag/application-domain-mark fallback.
* OriginalNeutralLeaf.refineInputs changes ONLY oldStep, using its endpoint/window neutral guard.
* OriginalVariableRepresentative.refineInputs first applies OriginalConstructorLeaf.refineInputs (oldStep only), then changes oldRepresentative by the variable-mark fallback.
* Thus r.base.oldSource/oldTarget/member are literally q.base.oldSource/oldTarget/member, and r.window=p.window. r.oldStep is several actual refinements, NOT q.oldStep.
* OuterSelection.data applies SpineApplicationTargets.selectedData, then BottomSource.selection: an additional spine-measure representative guard, BottomParameter normalization of oldSource/oldTarget, bottom-mark representative guard and exactly one normalizedMember installation. The resulting S1 has normalized source/target/member, not the raw fields of r.

The public `OriginalApplicationSidecarIdentityProof.actualOriginalApplicationSidecarSelectionIdentity` already identifies S1 with `OriginalApplicationSidecar.selectedData b.base b.window`, proves selected validity/rootGuard identities, and gives the exact before/after source,target,member identities. In particular S1.oldSource = BottomParameter.normalized q.base.oldSource and S1.member = normalizedMember q.base.member. BottomParameter.normalized substitutes the original context with zero Gamma only at exact bottom codes. It is not literal equality to the unnormalized source on all arguments.

## 2. A substantial INTERNAL bridge already exists; do not rebuild every guard

`OriginalApplicationSidecarTransitionGuardProof.actualOriginalApplicationSidecarGuardRedundancy` is stronger than native refinement: for arbitrary Data/window/body/Delta and arbitrary input/output/parameter it supplies an internal iff

`graph2 (selectedData data window).oldRepresentative out input parameter`
 iff `graph2 (OriginalApplicationSidecar.representative data window) out input parameter`.

No validity, observer invariant, native calibration or fixedness premise is required. Together with the selection identity above, this removes the whole observer-selection guard stack at S1.oldRepresentative. It preserves the **branched sidecar representative**, not the original data.oldRepresentative, and not the sidecar fold unconditionally.

The exact remaining branch is:
`branch (OriginalFunctionNeutrality.active data window) data.oldRepresentative (fold data window)`.
The active predicate is literally the conjunction of `BottomRepresentative.windowAt window` and validity of originalData data window. Its validity is independent of oldRepresentative; it is not thereby known to hold at today's concrete source terms.

Other checked internal suppliers:

* `OriginalApplicationSidecarWindowProof.actualOriginalApplicationSidecarWindowIndependence` transports the same windowAt graph between input coordinates at unchanged parameter. It does not create a window success fact.
* `OriginalApplicationSidecarTransitionProof.actualOriginalApplicationSidecarTransitionIdentification` identifies the actual bounded-descent transition with sidecar fold C under the actual window and originalData.sourcePremises. It identifies T with C, not q.oldRepresentative with C.
* `OriginalApplicationSidecarEquationProof.actualOriginalApplicationSidecarApplicationEquation` gives C's raw-application equation from actual originalData parent validity and actual C child graphs. It reconstructs applications, not arbitrary primary invariance of C.
* `OriginalApplicationSidecarSameLeafOutputProof.actualOriginalApplicationSidecarCanonicalOutputFixed` gives C(out)=out from an actual final canonical fold and its own source/window premises.
* `OriginalApplicationSidecarSameLeafProof.actualOriginalApplicationSidecarSameFinalLeaf` and `...SameLeafEquationProof.actualOriginalApplicationSidecarCanonicalApplicationEquation` give final leaf identity/application equations from actual canonical child outputs. They do not supply the missing source activation or C/coherent-primary transport.

Consequently the earlier idea that every neutrality/shape/variable/spine/bottom guard needs a new preservation proof is unnecessarily large. The guard-redundancy theorem already pays that stack **after sidecar installation**. The new nontrivial representative bridge lies at the active sidecar branch and its source-premise alignment.

## 3. The exact M/W mismatch must remain visible

The accepted primary/initial coherence source premise is
`TermAccepted H (OriginalUniverseDomainCoverage.member n) (OriginalGuardedHeadSourceCoverage.window n arity) typ raw gamma context`.

Write M0 and W0 for those concrete suppliers. In contrast q.base.oldSource uses
`Mp = InternalOriginalUniformContextMembership.contextMember p.base.member` and the arbitrary Program2 W. Additionally its final source validator normalizes bottom parameters/member fields as above. W is the head-window supplier inside the term checker; p.window is the separate Program1 global finite-window test. These two windows are not interchangeable.

`OriginalUniverseDecoder.source H G Mp W` is literally the conjunction of G(left parameter) and `termCheck H Mp W(left input,right input,right parameter,left parameter)`. Under observed input/parameter pairs, its exact source-success formula is therefore G(context)=1 AND TermAccepted H Mp W typ raw gamma context. The current premise instead supplies TermAccepted H M0 W0. No record identity changes M0/W0 to Mp/W.

Since p.member and W are arbitrary in acceptance103, their graph behavior may differ from M0/W0, including rejection of inputs accepted by the concrete checker. A generic implication from the current concrete acceptance premise to q.base.oldSource=1 is not justified. The initial coherence theorem did not need that implication because its rankguard theorem handled arbitrary source/window controls. The sidecar transition/application suppliers genuinely ask for their own validity/source/window observations.

Native `InputsCalibrated`, `ContextMemberCalibrated`, `HeadWindowCalibrated`, or all-vector evaluation equality do not produce an internal graph implication. `OriginalApplicationSidecarTargets.ActualOriginalApplicationSidecarRefinementEquality` is precisely such a native equality and cannot bridge this gap.

## 4. Existing validator-collapse theorems are not automatic solutions

`OriginalTransparentDecoderValidatorCollapse.GraphEquality` is the right kind of internal all-output equality. Its `SourceCollapse` and `FinalSourceCollapse` targets are already universal in arbitrary p/H/G/W, but the final selected Data is specifically
`OriginalLambdaTraversalSelection.finalData (OriginalVariableLeaves.refineInputs G (OriginalTransparentDecoderSelection.transparentInputs H G W p))`.
That is the lambda/variable-refinement pipeline, not S1 above by name alone. Moreover its RHS is the SAME supplied transparent source with Mp/W. Even if an exact structural adapter identifies an applicable validator, this theorem does not replace Mp/W by M0/W0. Native equality between two selected presentations cannot serve as that adapter.

Generic existing term acceptance constructor/inversion/transport APIs preserve their supplied H/M/W. The inspected universe targets do not provide a ready all-suppliers replacement theorem that silently discharges this mismatch. A supplier-transport theorem would need actual internal graph contracts and sufficient recurrence coverage; native calibrations are not those contracts.

## 5. Honest next steps, smallest first

1. **Small exact bookkeeping consumer, if useful:** specialize the existing selection identity + internal sidecar guard-redundancy theorem at b=q with spine leaf refinement. This gives a genuine internal iff from S1.oldRepresentative to the branched sidecar representative, without pretending it is q.oldRepresentative. No M/W bridge is needed for that narrowly stated result.

2. **Smallest unpaid source interface:** prove exact source success introduction/elimination for q.base.oldSource under actual input/parameter pairs, concluding precisely G(context) AND TermAccepted H Mp W. This uses original conjunction/composition/pairing APIs and literal field identity, not new syntax induction. It exposes the real missing supplier contract and prevents later callers from accidentally using M0/W0 acceptance. It is an interface theorem, not a discharge of the mismatch.

3. **Before active sidecar coherence, choose an honest source scope.** Either retain explicit actual Mp/W source and p.window success premises in a conditional internal theorem, or identify a concrete initial p/W construction and prove actual internal graph transport from M0/W0 to its Mp/W. A requested whole-source result must eventually pay that transport, not hide it as a new correctness field. Do not replace p by a native-equivalent witness.

4. **Active branch obligation:** at aligned actual source/window scope, prove that C has the required relation/coherence on original primary members (or a sufficiently strong internal graph equality from C to the already coherent initial representative). Existing application and canonical-fixedness equations can be used, but do not themselves supply this theorem. For the inactive branch, original initial coherence plus two actual zero-control observations suffices. To combine mixed active/inactive cases, one needs alignment of activity or genuine C-versus-initial output agreement; this is not settled by window independence alone.

5. **Then distinguish oldRepresentative from final normalization:** even successful S1.oldRepresentative coherence is not automatically selected bounded-descent or canonical-fold coherence. Use actual transition/fold equations at the same S1 and same source obligations; no equality of final tuples or generic all-term accessibility conclusion follows by calibration.

The immediate favorable finding is the unconditional internal guard-redundancy bridge. The immediate genuine blocker is source-supplier alignment plus the active sidecar C relation, not another set of native calibrations or blanket reproof of all observer guards.
