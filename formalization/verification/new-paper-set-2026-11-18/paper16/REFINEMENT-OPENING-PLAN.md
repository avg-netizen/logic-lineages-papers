# Fresh-opening synchronization before transitivity

Freeze Synchronize: for any two names of the binder type absent in both literal
bodies, an actual refinement tree between the first openings yields a tree
between the second openings with exactly the same explicit all-subtree count.
No body alpha quotient, transitivity, arbitrary substitution, E or cut premise.

Proof route: finite swap of the two Nat names at the specified type, identity
at other types. Prove involution/injectivity, absent-name identity on the actual
body, and mapping of the first free name to the second. Use already-checked
opening covariance and injective tree/count equivariance, then explicit
endpoint equality transport. Both old and new names are fresh; x=y is allowed.

This supplies a strictly count-preserving synchronization step for the already
frozen complete refinement Transitive target. Transitivity will induct on the
actual right tree count, after inversion of the left tree. Lambda choices are
synchronized to a fresh name absent from all three bodies, using the existing
finite fresh-name construction. Marked extras recurse on the right's genuine
extra-subtree witnesses, including its whole-owner witness, and use actual
retyping of the left whole-owner refinement. No self-composition assumption.
