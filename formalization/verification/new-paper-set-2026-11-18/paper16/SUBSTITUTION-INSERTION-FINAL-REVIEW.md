# Independent final substitution/insertion review

Accepted ten exact supporting raw-syntax laws. Independently reran the
read-only verify_substitution.py: eight local modules, ten exact aliases,
zero errors. Reconciled frozen source/target pins, actual source/dependency
input keys, compiler context, output bundles, native receipt membership and
log hashes. The aliases contain only standard axioms. Native first-pass
receipt1794976605743448950-2; no source/target repair reported or observed.

Read both proof modules and exact-alias checks. Structural mutual recursion
covers all Expr/Args constructors; lambda cases increment cutoff/depth.
The insertion proof explicitly handles retained, replaced and outside-block
indices, using lookup-none length bound before subtraction/successor algebra.
It does not assume away the out-of-block case. No strengthened input premise
or weakened conclusion was introduced. Seven algebra and three insertion
aliases correspond exactly to their frozen propositions.

The earlier pre-scope limitations remain: annotation preservation is not a
typing theorem, and these laws do not constitute full successful-application
substitution covariance, alpha correspondence or comparison soundness. No
numbered manuscript theorem, full-root build or CI completion is claimed.
This reviewer did not launch an additional compiler for the P16 review.
