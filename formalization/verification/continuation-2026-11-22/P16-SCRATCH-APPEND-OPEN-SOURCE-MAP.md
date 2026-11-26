# Paper 16: direct open scratch append preservation

Status: source-only candidate; native and axiom checks pending.

`exact_OpenScratchAppendMembership` is an arbitrary-body, arbitrary-context
rule for the original `InternalApplicationValidityStackAppend.append`. Given
its actual output graph and an object disjunction that the same candidate
is present in one of its actual two input lists, the conclusion is an
original `scratchMember` exact-one graph on that very output. The two
one-sided corollaries simply introduce the input disjunction.

It uses original list induction on the left physical list, with the
right list and candidate fixed. The nil branch rejects membership at zero
and uses the true append nil graph; the cons branch obtains the actual
appended tail and exact output cons, then uses head/recursive membership
at those physical codes. The intermediate composed membership call is
built and inverted from the actual append graph, with no numeric decoder
or proof reflection, invented tail result, converse, or primary theory.

| Module suffix | SHA-256 |
| --- | --- |
| `NumberedWindowInternalScratchAppendOpenTargets` | `66263ed26180239eb23fa0a36ccaa0818b1b9a19ed33c8c66456fbd093cc5bee` |
| `NumberedWindowInternalScratchAppendOpenSyntaxProof` | `de3bd00236c201dcb3db4efb24ba26b815151ebaf738ff011122ec90dc3e2eb0` |
| `NumberedWindowInternalScratchAppendOpenChecks` | `815ae08d1c67816dbf0675da28c9087f2adb5b0c3a25beb6ea2c4ade4a7f7214` |
