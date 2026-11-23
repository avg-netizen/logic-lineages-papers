# Actual policy-indexed comparison classification

`PolicyIndexedMainComparison` changes the positive clause relative to
#1429 from per-effective-policy existence to a primitive-recursive
index transformer selected before a supplied policy program index.
It uses the concrete indexed literal assignment and the unchanged
vector compiler, not a hypothesis that such a compiler exists.
Correctness is for implementing policy programs and encoded typed original
terms in a common ground context; it does not decide policy validity or
impose totality on arbitrary program indices or encodings. Every effective
literal selector has an implementing code by the checked #1430 result.

The closed-block query, positive coordinates, near-control laws and
original reductions are unchanged. For each fixed near-control
parameter there is a transformation uniform in policy; there is not a
separate assertion here of uniform compilation in the control parameter.
The original comparison is the weak, strict and equality relation on typed
expressions in a common ground free-variable context. Result, intermediate
and bound types are not restricted to ground type. The hardness reductions
remain the original policy-independent and control-independent reductions:
strict finite-query level one, equality finite-query level two, and their
single-query versions at levels one and three, respectively.

The exact main wrapper was checked in native receipt
`1795435569472093489-54` with standard axioms only. The first full native
attempt `1795435304010797948-13` rejected a namespace open in the proof
wrapper, not the targets, definitions or comparison algorithm. The rejected
proof's SHA-256 was
`42866a13909282e4b6703fbc3f2994fc81c545f71d08a5907c1710e8b3a851d9`;
the proof-only zero-context reverse patch (apply with `git apply --unidiff-zero`) is
[drafts/P17-POLICY-INDEXED-MAIN-NAMESPACE-REPAIR01.reverse.patch](drafts/P17-POLICY-INDEXED-MAIN-NAMESPACE-REPAIR01.reverse.patch)
(SHA-256 `0279548a3949497c557d5ec0b7b533b188dd9b8a9adf4a189d805c49e3fe8b87`). This is supporting evidence; it
does not change the numbered register.
