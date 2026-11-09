# Original outer path dispatcher with runtime Gamma

The definitions and three target propositions were reviewed and frozen before
proof authorship, against baseline
`9cbe6c5a6b999d5c34763075034cc05a428c990c`.

The source function is the unchanged
`ApplicationCertificateLiftPath.pathValue` on the original five inputs
`[context, domain, codomain, argumentObject, certificate]`. Its original Object
decoder supplies Gamma and the raw argument; its original `liftPath` keeps the
existing list of paired vertex/edge entries and the same edge transformer.

The new dispatcher selects its active branch only when the context equals the
chosen original finite-window code. The active branch computes
`pair(context, left(argumentObject))` using the original pairing/unpair ASTs and
calls the existing `InternalApplicationPathMap.pathMap` with
`[certificate, parameter, domain, codomain, right(argumentObject)]`. The supplied
vertex is the same uniform vertex already calibrated for every original Gamma.
No Gamma is captured in the dispatcher. The inactive branch is the complete
original oldLift with all five inputs unchanged.

## Exact targets

| Target | Original obligation and proof supplier |
| --- | --- |
| `ActualOriginalUniformObjectPathCalibration` | Full equality to original `pathValue` on every natural five-vector. `JointGammaDomainCodecProof.actualObjectCodec` and the original product-code identity expose the actual decoded Gamma externally; uniform vertex/map calibration gives the active branch, and original oldLift calibration gives the inactive branch. Data and both old programs precede every selected source window. |
| `ActualInternalOriginalUniformObjectPathActiveGraph` | In the original `InternalCalculus.Derivation`, actual left/right and pairing graphs at arbitrary symbolic GammaCode identify the supplied outer output with the same map output. The only additional local condition is the actual context equality that activates this dispatcher. Composition, equality-test and branch graph laws supply the derivation. |
| `ActualInternalOriginalUniformObjectPathZeroGraph` | The literal zero graph of the window test identifies the entire fallback graph, including its original output and all inputs. The existing generic zero-branch theorem supplies this law. |

The original oldLift witness is already supplied by
`ApplicationCertificateLiftPathPrimitiveProof.actualProgramWitness`; no new
existence or selection target is needed here. Original codec totality is used
only for external calibration, never as an internal reflection principle.

This packet closes the outer path-program graph boundary. It does not assert
the original outer typed/positive/result wrapper laws, the shared-Gamma witness
extraction from their antecedent, unqualified `CertifiedApplicationLift`, or
paper06 `lem:id1`. Those obligations keep their original statements. The
original one-calculus judgment, primitive-recursion graph compiler, codes,
boundaries and proof-resource profile remain unchanged.
