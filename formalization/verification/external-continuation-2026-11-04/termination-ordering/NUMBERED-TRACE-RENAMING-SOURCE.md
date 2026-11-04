# Exact-count forward renaming through traces and confined quotient representatives

Draft for review; no proof/export. Context/quotient prerequisites for paper 06 lines 583–597.

Packed, typed and tuple traces preserve the literal original count under arbitrary typed renaming: primary edges remain count zero, actual steps remain one, and composition adds the same counts. Unlike general substitution there is no collapse alternative.

The counted and positive quotient targets explicitly assume SubtypeClosed and confinement of both original packed endpoints. countBackward reconstructs their raw trace; exact trace renaming and countForward give the renamed representatives with exactly the same count. Positivity thus remains positivity. Representative congruence follows actual primary preservation and representativeEquality in both contexts.

No separate GoodRenaming assumption is hidden: a typed renaming retains variable types, and accepted actualRenaming preserves the fixed universe. Equivalently, its variable-valued substitution is automatically GoodSubstitution on window types. No new symbol/type-window membership is required for unused context entries. Noninjective renamings are allowed forward, so no reflection is claimed.

The numeric operations are stated on actual confined representatives, not a total numeric code map. Neither backward image closure, Acc/least-set/C stability, original-order transitivity, global computability nor ID1 follows here. Prior accepted bytes unchanged.
