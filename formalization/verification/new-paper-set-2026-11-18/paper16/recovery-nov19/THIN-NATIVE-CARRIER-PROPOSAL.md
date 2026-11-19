# Thin native carrier check, proposed only

The original owner-host `NativeCarrierChecks.exact_Carrier` compares the
same literal Q, C₂, C₁, C₀ terms and exact full calls of
`NativeCarrierTargets.Carrier` (frozen LANE-A-NATIVE-CARRIER-FROZEN).
The rechecked cloud invocation completed 224 of 225 rows. Its final
root observed 529120 KiB against the unchanged 524288 KiB cap and
exited 77: the axiom line printed before shutdown is not a pass. The original
source, stopped receipt, leaf log and full gate transcript are preserved.

`NativeCarrierThinChecks` is a new candidate root, not a modification of any
old proof. Its exact theorem has the same literal frozen target and proof
body. The only proof-dependency substitution is the local definitional
`appSupport` lemma, copied verbatim from the original
`NativeRSProof.appSupport` (an application inserts its result support
and both argument supports). The original import was used only for that
equation but brought in the unrelated recursion-successor theorem and
its heavy context/composition dependency graph. Static counts with the
respective roots: 225 modules before, 66 after. No ranked, closed, support,
typing, or companion-comparison condition is changed; no old semantics,
checker, core limits, or evidence is modified.

An independent equivalence-of-scope review and new serialized native ticket
are required before using this candidate. A resource-stopped old root is
not being retried unchanged.
