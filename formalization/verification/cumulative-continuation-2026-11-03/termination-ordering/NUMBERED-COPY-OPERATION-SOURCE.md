# Actual Copy operation and numeric certificate effectivity

Paper06 lines537–556 specifies the fixed-type numbered reduction, including
Copy to a lower-precedence unmarked head with self-arguments at the decremented
finite label, before forming the computable primary quotient and its arithmetic
edge relation. The existing `RawStep.copy`, `WindowStep.copy`, `copyTarget` and
`copyCertificateTest` retain that rule. This component requires effectivity of
those existing executable Copy operations; it does not introduce another rule.

The structural `copyCode` accepts precisely a positive-numbered source root
whose explicit result type is the target head's original result, whose source
head is above the target in the original `RecursiveComparison.headAbove`, and
whose target satisfies the original `HeadInWindow`. Its output is the target
ordinary head applied to the already checked literal `selfCode` construction.
Every self-copy retains the original source head, base, extra-type list and
extra arguments, changes its explicit result to the requested argument type,
and decrements the finite source label by one. Non-numbered and zero-labelled
roots return `none`; failed original guards return `none`.

Native result signatures remain the actual `headResult` values: ground zero,
functional successor, and the original case/recursor types. Native heads have
empty base lists; application has the original function/domain pair; ranked
heads use the original finite arity's repeated ground arguments. The accepted
head-signature and self-argument suppliers are reused. Auxiliary application
and original functional-head application are not identified.

Copy's target guard remains `HeadInWindow`, without replacing it by the
`sourceHeads` enumeration used in the separate exchange algorithm. The typed
operation acquires no source-head window guard. Its numeric certificate uses
the original source `decodeUniverse`, original `decodeHeadNumber` for the
certificate, original `copyTarget`, and exact target `packedNumber` equality.
Invalid numeric source/head encodings, invalid typed source data, failed source
universe tests, and failed Copy guards retain their original rejection. The
raw structural program is not claimed to validate arbitrary nested syntax;
its exact typed calibration and the unchanged numeric decoder provide that
boundary.

The five frozen targets require the original head-order decision, all-input
structural Copy, equality with the actual typed result map, genuine packed
Copy, and the unchanged numeric certificate test to be primitive recursive.
The finite precedence table varies inside the primitive-recursive input using
the existing nested `Fin`-function presentation. No transitivity, strictness,
well-foundedness, subtype-closure, source-universe, or assumed effectiveness
premise is added to these computational targets.

Finite signature size `n`, its actual arity function and binder context
`Gamma` remain explicit universally quantified fixed parameters. Both window
lists, the whole precedence table, target head/source code where applicable,
and the source/target/certificate numbers vary jointly. No uniform algorithm
over encoded varying signatures or contexts is claimed by this checkpoint.

This is an unpaid Copy supplier beyond the accepted original-source codecs,
translation, weakening/substitution, direct operations and Select. Whole
numeric root/step/edge/path effectivity, arithmetic presentation and the
remaining accessibility/ordinal source claims are separate obligations. The
existing local ordinary-domain transitivity obstruction is unchanged.
