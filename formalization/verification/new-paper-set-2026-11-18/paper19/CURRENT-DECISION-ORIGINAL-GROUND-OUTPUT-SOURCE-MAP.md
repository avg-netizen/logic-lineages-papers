# Literal original tree queries for both compiled ground outputs

Exact numbered source: paper19 observers.tex 37–51, with the literal
Boolean compiler of compiler.tex. Source allows scoped DAGs, but the
original tree-only interface must not use a noncomputable typed
projection to decode them. This additive packet closes that interface.

`asTreeQuery` keeps the exact shared arity from the first table context,
uses the actual original strictness flag, and calls literal
`CurrentTreeCode.expand` on both raw tables. `outputQueries` emits the
strict pair at true and the weak pair at false; no table, result term,
comparison direction, or arithmetic answer is changed. `toGroundTrees`
maps this over the exact in-force `toGround`, leaving all malformed
queries in the existing separate none branch.

`TypedReencoding` requires arity, flag and identical raw original
`SyntaxCode.encodeTerm d.term` from both typed ground DAGs in a shared
context. This requires `CurrentTreeCode.exactExpansion`, not mere
existence of some original spelling. `ArithmeticOutputs` instantiates
this on both real literal compiler outputs and must use the accepted
`CurrentCompiler.literal_outputs`. `OriginalOutputs` connects the new
literal pair to the same arithmetic witness and exact selected-policy
strict/weak semantics in the original-tree presentation target.
`Effective` records both unrestricted raw tree-code expansions
(containing no parser policy) and the composition with the actual
computable selected-policy/allowed f map. No decision oracle, no
feasible-size assertion and no transfer of an old fixed-policy claim.

Do not change any original-tree-coverage, original-tree-presentation or
numbered CurrentDecision source/pins. Freeze this new map and targets
before proof and ask for separate exact target-only preflight.
