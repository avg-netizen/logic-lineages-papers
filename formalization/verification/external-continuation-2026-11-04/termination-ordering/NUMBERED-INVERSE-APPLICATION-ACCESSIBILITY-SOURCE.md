# Typed successors and conditional inverse application accessibility

Parent reviewed exact targets and correspondence 2026-11-04 11:33 UTC. Standard comparator/freeze required before proof. No export or publication.

Paper06 lines583–589 uses the fact that function-side descendants remain descendants after applying a fixed argument. This component proves the conditional metatheoretic accessibility consequence for the actual finite-window quotient relation, not a computability or ID1 theorem.

ActualTypedSuccessorWitness starts with a confined typed q and an arbitrary numeric positive quotient successor y. It must derive a confined r of exactly the same type, rep(r)=y, and a genuine positive-count WindowTypedTrace q r. Accepted path lifting first yields a packed witness; same type must then follow from actual trace erasure and type preservation. No typedness/representability assumption about y is supplied.

ActualInverseApplicationAccessibility fixes a confined f:sigma→tau and confined a:sigma in the same binder context, signature, subtype-closed type window, symbol window, and precedence relation. If rep(applicationPacked f a) is accessible under reverse PositivePath QuotientEdge, rep(f) is accessible under that same relation. Subtype closure and both confinement hypotheses remain explicit.

The proof must perform genuine Acc induction on application accessibility. Every numeric successor of rep(f) receives the first target's typed confined witness; actual positive function-application path lifting supplies the recursive predecessor. No injectivity of application or representatives is required or assumed. No numeric successor, context change, or carrier obligation may be skipped.

This does not supply a computable argument, prove C_tau implies accessibility, alter positive application contexts, or infer global WF/ID1. It uses only function-side positive steps and preserves the original transitivity obstruction.
