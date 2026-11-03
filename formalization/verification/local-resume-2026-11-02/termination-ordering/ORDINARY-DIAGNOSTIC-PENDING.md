HISTORICAL pending snapshot; SUPERSEDED by checked four-gate1793669543703102170-2.
See ORDINARY-TRANSITIVITY-DIAGNOSTIC.md and exact ACCEPTED record.

# Pending original-domain beta diagnostic

Status: NOT ACCEPTED. Exact target frozen before proof in
OrdinaryBetaTransitivityDiagnostic-FREEZE.json. Positive original steps have
compiled; scalar/multiset exclusion and cyclic-budget gate remain pending.

All P,T,U below are ACTUAL Source.Term embeddings. Use ranked heads
Z < H < K < F with arities 0,0,1,2, k=K(H), and
P=(lambda x.F(x,Z)) k, T=F(k,Z), U=F(H,H). The concrete encoding uses
natural-number symbol names 0,1,2,3; no other symbol occurs in these terms.
q is the literal marked application with base [(lambda x.F(x,Z)),k].
Selecting the lambda with the whole q returns s=F(q,Z). Selecting k gives k.

Candidate obstruction: q cannot be positively strict-marked again. The finite
possible proof cycle is q -> s -> markedS -> q. Any candidate Fun proof from
s to U needs Z Weak H; any Stat proof from markedS to U needs a strict source
q or Z to H, or else violates the nonempty-removal/length conditions. Native
application cannot Copy to ranked F. Four simultaneous budget-n exclusions
are authored to prove this without any bounded proof-search cutoff.

Scope caution: even a checked counterexample would concern the IMMUTABLE
local RecursiveComparison rules and the exact frozen ordinary-domain target.
No refutation of Kop's published theorem is inferred without a separately
checked full source-convention correspondence. The actual source definition
and source faithfulness must be diagnosed separately; no accepted semantics
may be silently changed to make the target pass.

Primary reinspection: Cynthia Kop, Higher Order Termination, author-hosted
corrected thesis, https://www.cs.ru.nl/~cynthiakop/phdthesis.pdf, chapter 5
Definition 5.19, Lemmas 5.24-5.30 and Theorem 5.31. Read directly during this
checkpoint. Its stated theorem is background being compared, not an axiom
or a proof supplier for this finite local diagnostic.
