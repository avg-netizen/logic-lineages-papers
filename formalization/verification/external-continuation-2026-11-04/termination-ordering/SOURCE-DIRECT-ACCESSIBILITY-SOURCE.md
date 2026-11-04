# Actual decoded-list accessibility bridge

Parent reviewed exact targets and correspondence 2026-11-04 11:09 UTC. Standard comparator/freeze required before proof. No export or publication.

Paper06 lines598–603 motivates multiset accessibility from accessible members; lines551–556 provide the numeric quotient relation. This component specializes the accepted generic member-accessibility theorem to the actual positive quotient-path relation Rctx, using the exact Context n symbols, type window, and Boolean precedence table. There is no replacement relation or transitivity assumption.

ActualListAccessibility assumes MembersAccessible Rctx values, meaning every original list occurrence's value is Acc under (fun successor source => Rctx source successor), and concludes Acc for reverse literal Direct Rctx on that list.

ActualDecodedAccessibility includes exact successful witnesses Encodable.decode context = some ctx and Encodable.decode code = some values, with the same member premise. The conclusion is Acc (fun successor source => encodedDirect n arity Gamma context source successor) code. A genuine Acc induction on the literal-list result must cover every encoded successor: decode uniqueness aligns the edge's context and source list with the fixed witnesses, and the target's actual decode witness supplies the recursive call. The arbitrary code need not be syntactically given as Encodable.encode values. Malformed codes are not silently accepted or repaired.

No SubtypeClosed, canonical carrier, type-indexed typedness, ambient irreflexivity, transitivity, or global WF assumption is needed or added for this conditional accessibility statement. Source-member accessibility remains explicit. Concluding membership in the previously constructed semantic least set would separately require actual encodedList membership and decoded subtype closure; that conclusion is outside this component. No C_tau, ID1 derivation, all-terms termination, or register promotion.
