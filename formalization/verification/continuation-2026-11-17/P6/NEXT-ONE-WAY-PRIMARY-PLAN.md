# Next one-way primary coherence: reuse existing internal inductions

Read-only audit after OriginalCommonCandidatePool. No target/proof/acceptance claim.

Goal under the same original source scope, actual c in L(s,p), and independently observed actual L(c,p)=targetOut: every member of targetOut belongs to sourceOut=L(s,p). Equivalently an internal PrimaryMonotonicity.included targetOut sourceOut, if the binder-context proof is packaged. No symmetry, reverse reachability, representative equality or output-code equality is needed or follows.

No generic least-closed-carrier endpoint was found in the relevant continuation target families. However the required arbitrary symbolic count inductions already exist:

- PrimaryMonotonicity.InductionProof.iterationMonotonicity: included initialLeft initialRight plus actual iterate graphs at SAME pool/count/parameter implies included leftOut rightOut.
- PrimaryStability.InductionProof.iterationStability: actual expansion first of initial, included first initial, and actual iterate output at arbitrary symbolic count imply included output initial.
- LengthAlignedPrimary.InternalProof.internalEdgeClosure: actual admitted primary output is closed for actual E edges whose new target is in its observed pool.

Suggested short proof chain:

1. Derive candidate admission and query both actual Q/pool outputs internally. OriginalCommonCandidatePool supplies membership equivalence of candidatePool and seedPool at an arbitrary probe under weakening/relabeling. The public one-way endpoint need not retain Q/pool graph observations if programCases handles these witnesses.
2. Query actual expand(E)(candidatePool,sourceOut,p)=first. Prove included first sourceOut by InclusionProof.introduce and PrimaryExpansionSoundness.Proof.expansionCharacterization: old-member branch is direct; new-member branch carries candidatePool membership and a sourceWitness from sourceOut. Transport pool membership to seedPool with common-pool result. Eliminate the existential witness and apply internalEdgeClosure at the original seed primary. This is the only new mathematical closure step.
3. Decompose actual primary at candidate into actual run E at its own internally queried countOfPool(candidatePool) and candidatePool. Do NOT assert equality of cutoff terms or cardinalities of membership-equivalent pools; duplicates may change lengths.
4. Recover the literal singleton candidate and actual iterate graph using the generic run AST helper already used in OriginalPrimaryUniverseClosure.RunGraphProof.recover (generic E). Candidate membership in sourceOut gives included singleton sourceOut by singleton membership equality and equality transport.
5. Query the actual iterate from sourceOut at that SAME candidate count and candidatePool. Existing iterationMonotonicity bounds candidate's iterate by this queried output. Existing iterationStability bounds that output by sourceOut using step2. Compose inclusions using InclusionProof.introduce/eliminate (or the existing inclusion transitivity helper if found).

All total-program query witnesses must be handled by capture-free relabeling and stronger contexts, not extracted as external naturals. The exact original source scope still includes ArrowClosed tied to the observed types selector, original context guard and seed universe acceptance. No assumption says E is symmetric, nor that target admission alone entails original universe acceptance.

This approach avoids a fresh all-count inductive invariant and avoids recompiling another concrete-E induction. New generic closure/composition helpers should abstract fixed E/T/P and graph terms to keep the original 2048MiB heap/1536MiB RSS/2048MiB free-memory profile unchanged. Any final caller must discharge the generic closure premises with actual original suppliers above, not expose them publicly.
