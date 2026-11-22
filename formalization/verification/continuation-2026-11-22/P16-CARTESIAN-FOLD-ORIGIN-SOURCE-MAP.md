# P16: exact backward Cartesian source occurrence

Draft source-only, not a native gate or a numbered-claim promotion.

`NumberedWindowInternalCoverCartesianFoldOriginChecks.exact_OpenCartesianFoldOrigin`
matches frozen `ExactOpenCartesianFoldOrigin`. The original `flatGraph D out raw params`
and `memberGraph out image` yield one object witness `source` with literal
`memberGraph raw source` and exact one from physical scratch membership on the
actual D-generated block. Its tape is `[source,image,params…]`; the D input
selector drops only image, retaining source and params in their original order.
The separate `blockMemberOfHit` recovers the physical member test given the
actual D report at that same source and parameters.

Induction uses the original scratch list constructors. Nil has the real zero
fold and the real membership test cannot return one. A cons exposes the actual
recursion tail result and original head D block, recovers their actual append,
then splits the hit using the accepted backward append alias. Head establishes
membership in that same cons; tail eliminates the inducted existential and
carries that very witness into the original cons. No ordering or multiplicity
change, numeric reflection, named-leaf inversion, or whole-stage transport.

Static project import roots (including the roots themselves):
- Targets: 872 project modules; direct Hydra/Linarith imports here: none
- SyntaxProof: 1175 project modules; direct Hydra/Linarith imports here: none
- WitnessProof: 1199 project modules; direct Hydra/Linarith imports here: none
- Checks: 1249 project modules; direct Hydra/Linarith imports here: none

Exact source pins:
- `NumberedWindowInternalCoverCartesianFoldOriginTargets.lean`: `d5514058af486370ce56ee802d6a126a1f25f7994e86bafb1a30c2c272f1dace`
- `NumberedWindowInternalCoverCartesianFoldOriginSyntaxProof.lean`: `c8ed8deae98f8b85a77eb167a3d4e1da2543fef2e32590e7b0e4238fdcb7b870`
- `NumberedWindowInternalCoverCartesianFoldOriginWitnessProof.lean`: `e77420ceb271fc925ba07a12beaaf6c52983947f96dcb0a2f79e71eb9da4882b`
- `NumberedWindowInternalCoverCartesianFoldOriginChecks.lean`: `d300cbcf221a1d2ac5458b6ff61a394bf8b1acb30a27be21010e1a3fa81e19d1`
