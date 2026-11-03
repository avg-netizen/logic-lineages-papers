# Numeric wrapper for the exact guarded Mul checker

The wrapper decodes an actual in-universe source, an actual typed target at the same signature/context, and a literal occurrence-sensitive multiset certificate. It then runs the accepted typed Mul checker. Target confinement is not assumed or used as a rejection shortcut; it follows from actual typed Mul preservation. No SubtypeClosed or precedence assumption is needed for this rule.

Two targets prove existential numeric certificate acceptance exactly equivalent to a genuine guarded Mul instance with source confinement and exact packed codes, and accepted-certificate soundness to the actual WindowStep with both endpoints confined. Completeness uses the concrete packed and certificate roundtrips; soundness uses their successful-decode equality and the accepted typed checker. The base-only multiset relation, original extras, literal head guards, multiplicity and permitted witness reuse are unchanged.

This composes accepted interfaces to give a numeric Boolean certificate checker for Mul only. It does not decide every WindowStep, prove an arithmetic representation, establish quotient accessibility, or alter the original comparison rules/transitivity obstruction.
