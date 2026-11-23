# Actual policy-indexed comparison classification candidate

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
Native check is pending through the intermediate source and ground-driver
packets, and no numbered promotion is made by this candidate.
