# Original internal multiplication: checked supporting component

The existing calculus now derives left zero, distributivity over addition
in the right argument, and associativity for the original multiplication
symbol, for arbitrary ordinary terms and an arbitrary fixed positive body.
These are actual PA-induction derivation trees with no extra premises or
semantic reflection.

All three frozen exact aliases compile with only propext and Quot.sound.
The focused source closure has 726 source-matched modules. Frozen targets
compiled before candidate authoring. One failed candidate is preserved:
two arithmetic wrappers required rewriting the original equality embedding
before exact application, rather than simpa. Targets and semantics unchanged.
The original bounded serialized checker was used with 2,048 MiB heap,
1,536 MiB RSS, 2,048 MiB minimum free and one compiler thread.
See NATIVE-VERIFICATION.json for measured peak and source/evidence hashes.

These arithmetic suppliers support later beta coding. They do not establish
beta totality or uniqueness, finite sequence coding, general primitive
recursion, C_tau closure, accessibility or whole internal ID1. II5 is
excluded; target counts unchanged at 167 checked, 2 inherited, 20 pending.
No root build, remote CI pass, merge or changes to existing sources claimed.

Independent read-only review accepted frozen statements, original calculus
correspondence, exact aliases and the preserved repair. Closure receipt
matching was separately verified by the integrating author.
