# Accessible-element subtype: exact occurrence lift

Parent reviewed exact targets and correspondence 2026-11-04 10:56 UTC. Standard comparator/freeze required before proof. No export or publication.

Paper06 lines598–603 uses individual accessibility of multiset members. This generic prerequisite removes no hypothesis by fiat: AccessibleElement R consists literally of elements equipped with Acc (fun successor source => R source successor). LiftedRelation R a b is R a.val b.val, in source-to-successor order.

DirectMemberClosure derives accessibility for every target member from accessibility of source members and actual Direct witnesses. Kept occurrences inherit source accessibility through source permutation; every inserted occurrence has a removed dominator, whose membership in the source is derived from the same witness. Acc.inv then supplies inserted accessibility. No closure assumption is added.

OccurrencePreservingLift constructs a list of accessible elements whose erased list is literally the original list, not merely a permutation or set equality. Thus length, order, and repetitions are retained.

ExactLiftedDirect applies to arbitrary lists of AccessibleElement R, not to an assumed special canonical lift. It is a biconditional for literal Direct with its kept/removed/inserted lists, two permutation witnesses, nonempty removed list, and per-inserted-occurrence domination. The reverse direction must derive accessibility for all witness pieces, lift them, and prove the permutations through injectivity of Subtype.val. Duplicated occurrences and permitted dominator reuse remain unchanged; empty insertion remains valid deletion.

No ambient irreflexivity, transitivity, well-foundedness, decision procedure, or additional carrier is assumed. This component does not prove the final accessibility transfer theorem, global WF, or an ID1 derivation. Deriving accessibility on the subtype and transporting list accessibility back is a separate later obligation.
