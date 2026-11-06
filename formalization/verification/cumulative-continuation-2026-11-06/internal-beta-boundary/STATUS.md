# Original discrete boundary and beta wraparound

The original strict-order formula now has an internal discrete boundary
theorem: s<t implies succ(s)<t or succ(s)=t. PA induction on the original
strict-bound witness constructs this result; no semantic order decision,
replacement relation or extra premise is used.

The original beta formula now has the wraparound successor transition:
beta(a,b,i,r) and succ(r)=modulus(b,i) imply beta(succ(a),b,i,0).
The proof explicitly increments the original quotient and uses the
original multiplication-left-successor derivation, also supplied here.

Both new exact boundary/wraparound aliases and the multiplication supplier
alias passed standard-axiom audits. Boundary and multiplication use
propext/Quot.sound; wraparound additionally uses Classical.choice.
The focused boundary gate has 754 source-matched local modules; the
multiplication alias is checked by its separately retained supplier receipt.
Cited peak RSS is 1,226,832 KiB under unchanged limits: 2,048 MiB heap,
1,536 MiB RSS, 2,048 MiB minimum free, one compiler thread.
Final main and supplier compiler logs are warning-free.

Three failed main candidates are preserved with native evidence. Repairs
qualified a substitution lemma, directly constructed an existential
derivation instead of eliminating Nonempty into Type, and normalized the
original order embedding consistently in the local context. Frozen
statements and original sources remained unchanged.

This completes the two arithmetic successor cases, not yet their assembly
into general beta output existence. General existence, uniqueness, sequence
coding, primitive recursion and full internal ID1 remain open. II5 excluded.
Register unchanged: 167 checked, 2 inherited, 20 pending.
No full-root build, remote CI pass, merge or force-push is claimed.

Independent review accepted original targets, exact aliases, repairs and
reconstructed the complete 754-module source closure across 41 receipts.
