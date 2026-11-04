# Literal variable root behavior

Draft requested 2026-11-04 12:13 UTC; exact review required before comparator/freeze and proof. Verification-only, no export.

Paper06 lines583–589 includes the variable computability claim. These targets establish only its literal root prerequisites against actual NumberedWindowEquivalence.WindowPrimary and NumberedWindowReduction.WindowStep, not computability itself.

First, any actual primary-equivalent packed term to a fixed typed variable is exactly the same packed variable. The equality preserves the original type and de Bruijn variable, not just an erasure or numerical index. Quantification is over arbitrary symbols, arity, window, context and actual Variable Gamma tau; it does not manufacture a variable in an empty context.

Second, an actual WindowStep from this variable to q holds if and only if q is the literal bottom of the same type. The reverse implication uses the existing bottom constructor, since variable and bottom are disjoint constructors. Thus variables are not terminal. No source or target confinement, subtype closure or precedence assumptions are required for this raw root characterization; these would be needed later when connecting to a finite numeric carrier.

Primary reflexive/symmetric/transitive closure must be handled genuinely without assuming the desired rigidity. Exact variable view/injectivity can establish an invariant across all primary generators. Positive reduction excludes application-argument positions as before; no new rule is introduced.

No variable-headed spine accessibility, lambda/substitution computability, semantic least-set membership, arbitrary-precedence diagnostic, all-term theorem, ID1 derivability or original-order transitivity is included.
