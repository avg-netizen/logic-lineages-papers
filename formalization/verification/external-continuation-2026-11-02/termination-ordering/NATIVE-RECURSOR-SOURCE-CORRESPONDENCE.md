# Native recursor orientation — fresh exact comparator

Source: `06-godel-t-termination-ordering/paper.tex`, lemma `lem:recursor`, lines488–522 (displayed families and proof). Both original rewrite rules decrease under the actual confined strict comparison. The two target propositions quantify arbitrary finite ranked signature and precedence, context, result type (including arrows), and literal ordinary inputs. No strong-pair/transitivity or orientation premise is supplied.

`recursorTerm n A B` is literally `((Rτ n) A) B`; the successor contractum is literally `(A n) ((Rτ n) A B)`. `ConfinedStrict` retains the original mutually inductive Strict comparison on marked embeddings and exact RHS typeSupport inclusion into redex typeSupport. The zero target selects B, not a transformed term. The successor target is not limited to closed/ground inputs or a particular ranked signature.

The four typed families P, C2, C1, C0 have exactly the source original application/native heads, unchanged base lists, ordered simultaneous extra lists and output annotation ρ. C0 carries three extras at ground, H, τ; H is ground→τ→τ. Native recursor precedence over application is built into actual `headAbove`, independent of user ranked precedence. Intended derivation: original simultaneous Select prefixes, zero-argument Select through extras, accepted ordinary context closure of S n > n, then two native Copy clauses. No derived comparison relation substitutes for Weak/Strict.

Complete both targets before claiming the whole lemma. The subsequent all-reductions corollary also requires beta and case orientations and is not claimed here. Neither stability nor well-foundedness follows from this component.
