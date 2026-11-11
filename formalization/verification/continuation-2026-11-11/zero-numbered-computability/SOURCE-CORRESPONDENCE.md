# Label-zero actual numbered computability

Source: `06-godel-t-termination-ordering/paper.tex`, lemma `lem:id1`, the numbered-constructor computability paragraph beginning at line 605. This packet proves only the label-zero base case, not the general precedence/label/multiset induction or all-term accessibility.

The original `NumberedWindowReduction.WindowStep` is retained at the same `symbols`, subtype-closed `S`, precedence `above`, ambient `Gamma`, and result `tau`. At label zero its exact root/context alternatives are bottom, reduction in a base member, and reduction in an extra member. Positive-label Select/Copy/Mul/Abs are excluded by the literal constructor index, not by a premise about precedence.

The primary invariant retains the literal label and the multiset of typed least-code immediate members. `OneMemberReplacement` is only the explicit permutation witness for one child quotient edge; it never replaces `WindowStep`, `QuotientEdge`, its positive path, encodedR, or the calibrated scalar.

The final contract assumes actual Computable for all original base and extra members and proves actual Computable for the numbered node at the SAME context/scalar. It assumes no accessibility of that node, successor closure, rank certificate, observer soundness, or native-to-internal bridge. The intended proof derives member accessibility, uses the accepted actual direct-list accessibility theorem, then applies genuine native neutral expansion and downward closure.

Definitions, Targets and Preflight form the exact packet. They require coordinator freeze and preflight before mathematical adoption. No compiler or Git action is performed by this author.
