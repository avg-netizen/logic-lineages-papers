# Exact independent alpha characterization and named roundtrip

AlphaExact and DecodeEncodeAlpha pass final native receipt
`1794981097131451887-2`, under unchanged original core profile and unchanged
frozen definitions/targets. Recursive verifier reconciles 20 modules and two
aliases with zero errors, only propext/Quot.sound.

Converse encoding equality implies the independently generated Alpha relation.
At lambdas, choose one numeric name above both binder names and all names in
both bodies. The checked OpeningBridge turns the original encoded-body equality
into equality of the two actual capture-safe renamed bodies. Recursive
completeness applies to their strictly smaller constructor count; renaming
preserves that count. Actual Alpha.rename/lam/trans/symm reconstruct the desired
binder equivalence. Every head, base and extras constructor remains literal.
No encoding-equality premise is installed as an Alpha constructor.

The named decode/encode roundtrip follows from this actual converse, automatic
scoping of encoded named syntax, and the previously checked scoped canonical
roundtrip. All-environment forward alpha preservation remains checked separately.

Failed receipts 1794981054482490497-2 and 1794981077338186238-2 retain proof
sources. Repairs are limited to simplification of branch equations in the
termination obligations and tactic sequencing after solved goals. No target
or semantics changed; unused-simp warnings remain harmless.

This closes the frozen syntax-level alpha characterization and roundtrips.
Operation/clause correspondence for the comparison presentation is separate;
strict inclusion, ordinary reflexivity, cut/decision and full manuscript proofs
are not asserted by these results. No full-root build or CI claim.
