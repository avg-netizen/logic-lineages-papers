# Independent numbered induction memory split review

Approve implementation-only split for native checking. Compared current caller with preserved failed original. Exact public step statement is text-identical. Only helper import and tail after existing BelowRaw renaming change; query/witness/rename prefix remains intact.

New atValues helper abstracts existing renamed values, not programs or mathematical assumptions. It derives length from the same observations, builds the two child frames from the same original accepted argument checks and measured child bounds, derives strict descent from the original numbered constructor, instantiates the existing BelowRaw induction for both children, and supplies resulting child conclusions to the original NumberedCoreProof.atValues. The caller supplies original halj/harj/ihj and the identical ys slots (0..6,8,9); unused slot7 remains unused, not silently repurposed.

There is no added public success/induction premise, changed constructor AST, relaxed guard, dropped numbered metadata, or new axiom. Helper imports the original providers without importing its caller. Source-only approval, no native result or additional supporting credit. Current caller and helper hashes are recorded separately.
