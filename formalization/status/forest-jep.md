# Forest joint embedding formalization

Local main-thread research is **paused** by user direction for the
29 October 2026 10 p.m. Chicago cutoff. No compiler or mathematical author
is running from this stream. Resume only on an explicit instruction, beginning
with the graph representation and embedding-reflection targets below.

The user resumed local formalization on 29 October 2026 after external
checkpoint `abb52d9`. Main now owns paper 03 and
`LogicLineages/ModelsAlgebra/Forests/`; the models lane owns papers 01 and 15.
The existing checked host reduction, finite-code semantics and primitive
recursive tests remain the starting point.

## Current certificate proof

The fixed external `CertificateSearchTargets.lean` specifies the actual
finite-order-forest JEP predicate, exact certificate verification, sound search
outputs, existence of a certificate exactly on JEP failure, the search domain,
and malformed-family rejection. Main recompiled the unchanged targets before
writing its new candidate, receipt `1793309107664612843-2.json`.

`CertificateSearchProof.lean` and its seven exact semantic gates passed in
`1793310659443056183-2.json`, alongside the actual primitive-recursive verifier
and partial-recursive search gates. Compiler-directed repairs addressed decoder
simplification and logical rewriting, preserving the existing target types.

The new `CertificateFullTargets.lean` was separately compiled, hashed and
frozen before composing the full theorem from those accepted components.
`CertificateFullChecks.fixed_fullNegativeCertificateSearch` then passed in
`1793310861481589035-2.json`, with only the three permitted standard axioms.
It closes all nine semantic/effective clauses of the full source contract;
paper 03 **`prop:certificate` is checked**. Exact scope and portable audit output
are recorded in `Forests/ACCEPTED-RESUMED.json` and the global target register.

The proof connects the literal finite verifier and partial-recursive search
to the original mathematical JEP predicate. It does not assume Carter's theorem,
a bound on the first bad pair, or an arbitrary forest-bundle encoding oracle.

## Further paper obligations

The comparability-graph correspondence, Carter's positive decision supplier,
full width classification and countable age realization remain separate work.
The common-host bound applies to each fixed input pair; it does not bound the
first obstructing pair in terms of the forbidden family.

Compilation uses the existing serialized helper and the measured external
Mathlib resource profile. A compiler reservation is distinct from waiting for
user input. The Claude coordinator and both native lanes share compiler turns;
no additional native compiler ran during R004's author-held resource lock.
The reviewed R005 policy permits a read-only author alongside one native
compiler with sufficient headroom, unchanged caps and observed memory checks.

The next graph-bridge definitions and exact targets are also written.
`GraphExclusionProof.lean` proves the source P4/C4 exclusion using two
consecutive incomparable-endpoint forks. Its exact gate passed in
`1793310659443056183-2.json`, using only `propext` and `Quot.sound`.
Representation, uniqueness and the reverse embedding direction are not
assumed and remain pending. The complete `lem:bridge` is not yet checked.
