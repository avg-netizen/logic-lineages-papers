# Independent near-control effectivity pre-scope review

Approved for proof authoring/native exact checking. All three frozen pins match.
The target applies Primrec to the literal initialLcm and integer-remainder
correction definitions, and Primrec₂ to the literal two-parameter nearControl.
The latter establishes uniform primitive recursiveness in b,n, stronger than
merely asserting each fixed-b instance is primitive recursive. There are no
supplied abstract functions, changed remainder semantics, domain restrictions,
or effectivity assumptions in the proposition.

Current controls.tex lem:control and its opening proof explicitly assert this
near-control effectivity. Computing an auxiliary natural correctionCode is
permissible only with a proved equality to the existing integer correction;
no source definition replacement is authorized. The same applies to a bounded
search implementation of gcd/lcm. Native proof and recursive evidence remain
pending. The factorial f_* portion and full numbered lemma are not covered.
No compiler run by this scope review.
