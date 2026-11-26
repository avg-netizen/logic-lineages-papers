# Bounded representation repair after native RSS stop

Original fixed-core preflight1794982242334680704-2 stopped at ExtendedComparison
with exit77/RSS safety stop. Refinement and AuxiliaryWitnesses passed. Original
ExtendedComparison, accepted freeze, receipt and logs are retained under
failed/auxiliary-resource-1794982242334680704/. No limit increase or blind retry.

The proposed draft replaces seven mutually inductive Type families by one
Type family ExtendedTree indexed by a disjoint ExtendedJudgment tag. The tags
are weak/strict/matching/multiset/coverage/whole/ordered, with exactly the old
endpoint indices. Named old type families become abbreviations to their exact
tag applications. The intended reduction is generated recursor duplication,
not omitted semantics. All25 constructors and every premise are retained:
15weak;1strict;2matching;1multiset;2coverage;2whole;2ordered. Unique constructor
names replace reused nil/cons/intro names where needed. Proof-tree size must
continue counting every recursively stored comparison/list/Whole/ordered
premise. No casts, untagged supplier, generic composition or embedding constructor.

AUXILIARY-FROZEN.json remains the last accepted original manifest while review
is pending. Proposed current draft hashes are in
AUXILIARY-TAGGED-FROZEN-PENDING.json. Independent clause-by-clause comparison
must approve all premise fields, index endpoints and abbreviations before that
pending manifest replaces the accepted one or any native retry occurs. The
nine frozen target proposition texts do not change. This is not a parser-only
repair and must not be described as one.
