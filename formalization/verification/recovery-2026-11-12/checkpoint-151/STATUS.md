# Verified residual auxiliary proofs

Three unchanged auxiliary proof modules passed the normal bounded native checker and standard-axiom audits, and their entire source/object dependency closure is revalidated here.

- StructuralNodeSizeInternalMachineTerminationProof: three audited theorems for sufficient-budget termination of the actual encoded structural node machine.
- StructuralNodeSizeInternalMachineSaturationProof: two audited theorems for two-way state saturation of that separate structural metric.
- HereditarySourceRootBranchProof.branchBound: a valid but unused/superseded supporting bound; the accepted final source-root chain uses InitialBranch instead.

There is no new standalone pre-proof comparator or exact StatementChecks endpoint for these auxiliary modules. No such provenance is invented, and exact_aliases is intentionally empty. This is verified supporting source, not a new paper theorem or semantic completion claim.

All existing recovery freeze hashes remain valid and unchanged. Original aggregate and historical recovery limitations remain unchanged. No full-root or remote CI claim. Register unchanged: 171 checked, 2 inherited, 16 pending /189.
