# Finite profile supporting contract

Source entries.tex relative profile definition and equal-gap proof's joint breakpoint refinement. This packet supplies literal primitive-recursive raw profile computation, its actual ordinal correspondence, and finite coverage/constant pieces on [2,E). It is supporting only, not prop:equal-gap.

The total code algorithm traverses raw CNF via a course-of-values table, summing precisely those coefficient weights whose exponent compares >= the query. Invalid normality does not undermine total computability; actual semantics are asserted only for normal notations.

The semantic representative list includes 2, all actual two-prefix CNF exponents, and their successors, filtered by 2<=e<E. This is a finite cover, not yet the printed highest-piece selector: interior successor representatives may replace a maximal point only for this covering result, because the exact piece relation proves both profiles constant. The full algorithm must still use/prove the printed highest-piece selection and actual traversal.

There is no assumption of a profile supplier, partition oracle, no-skip, phase visit or effective eventual-order theorem. All x on [2,E), arbitrary ordinary CNF prefixes and breakpoint equality cases are included. E<=2 has genuinely empty domain. This packet does not claim a computable representation of the semantic representative list yet; that is separate finite-algorithm work before full equal-gap effectivity.
