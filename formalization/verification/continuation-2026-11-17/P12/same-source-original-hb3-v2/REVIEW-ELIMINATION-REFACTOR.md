# Independent elimination refactor review

Compared the complete current EliminationProof against the preserved failed-final03-heartbeats source. All five theorem headers remain byte-identical; inputBody and assemble are unchanged. Added only the generic helper import, local irreducibility annotations, and proof implementation changes. No comparator or original AST modification.

Generic doubleEliminate is precisely the old two successive uses of original HBQuantifier.existentialElimination, first at context one with weakened closed B, then context zero. It adds no premise and preserves capture avoidance. Generic weakenApply proves naturality for arbitrary Term ctx using original formula substitution composition and reflexivity; it does not assume the concrete desired equality. The specialized weakenProv uses that lemma then existing valueSubst. closedValue now states the context-zero substitution explicitly and invokes the same original valueSubst theorem with explicit dimensions.

Approved these exact pins for native retry under unchanged limits. This is not native success or complete HB3 acceptance.
