# Strict inclusion, ordinary reflexivity and mark encoding

All three frozen endpoints pass first native attempt `1794981370270108885-2`.
Recursive verifier:27 modules,3 aliases,zero errors; propext/Quot.sound only.
Frozen definitions/targets and original core caps unchanged. Unused-simp
warnings do not affect checked closure.

Strict inclusion peels the actual successful persistent mark: a head uses Put,
a marked node uses the given derivation, variables are impossible, and a
lambda uses the actual Abs fresh opening. Successful marking preserves free
names and commutes with actual simultaneous bound substitution, supplying the
opened successful mark internally. Recursion decreases original successful
mark-spine depth, unchanged by opening; no comparison closure is assumed.

Ordinary reflexivity uses Var, actual head equivalence and identity occurrence
matching, and Abs with a constructed fresh name. Opening typing, signature
validity, ordinariness and exact constructor count are derived. The recursive
opened body has fewer constructors than its original enclosing lambda. Root
bound variables are excluded by actual empty-context typing, and marked nodes
by the ordinary premise.

MarkEncoding relates the two existing actual persistent marking operations
under every named environment, including variable blocking and marked owners.
Together with already-reviewed target ordinariness, alpha/typing/validity and
opening, these are the complete constituent proofs of lem:elementary on the
source-permitted presentation. Independent final review and separately frozen
full numbered assembly are still required before registering that full lemma.
No structural stability, cut, decision, full-root build or CI claim.
