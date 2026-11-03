# Exact guarded typed Mul certificates

MulInstance copies exactly the guarded numbered Mul constructor: a successor label, output equal to the target ordinary head result, actual headEquivalent, target HeadInWindow, and the actual PrimitiveMultiset relation between ordered base lists. Original source extras are retained in the source and are not added to the multiset comparison. The checker uses the accepted occurrence-sensitive certificate without cancellation, deduplication, or an injective matching restriction.

Two targets prove certificate existence exactly equivalent to that constructor, and soundness for any actual precedence relation with target confinement derived from source confinement. The latter does not need SubtypeClosed: the target output is the source output, the target head is explicitly guarded, and target base confinement follows from actual primitive marking and retained occurrences. No target Good condition is assumed or checked in place of this proof.

This is a typed executable checker only for Mul. Numeric certificate encoding, complete WindowStep checking, arithmetic representation and quotient accessibility remain separate. Original comparison rules and the transitivity obstruction are unchanged.
