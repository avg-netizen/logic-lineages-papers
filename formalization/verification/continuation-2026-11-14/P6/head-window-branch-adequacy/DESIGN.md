# Internal original head-window branch adequacy (exact3)

Original source: NumberedFiniteUniverse.HeadInWindow, headArguments/headResult, and actual OriginalHeadWindow.branchWindow. Simple raw tags0..3 have no argument membership guards; their result-type computation remains an explicit graph of the actual branchResult AST. Application tag4 requires actual type membership of tau, arrow(sigma,tau), sigma; literal numeric arrow code is suc(pair sigma tau). Ranked tag5 requires symbol membership and ground membership. Actual arityAt lookup is NOT assumed correct: internal totality/zero-successor elimination discharges its branch, since ground result membership already supplies every ground argument test.

All statements are exact internal derivability equivalences for actual raw pairing graphs. No typed-list premise, native oracle, Boolean-output range assumption or replacement enumeration. No modification to accepted ASTs. Optional-layer Some0/Some1 conventions unchanged.

Source completeness caveat: NumberedFiniteUniverseProof.headWindow and NumberedAuxiliaryEnumerationSupportProof.headMembership require SubtypeClosed to infer cases/recursor payload membership from result membership. This packet does NOT omit that obligation or claim sourceHeads membership follows from window acceptance alone. Raw-window converse, internal subtype closure, decoder adequacy, argumentEntries/permutation semantic adequacy and full recursive E remain open.

Frozen definitions/types only, no proof/compiler before review.
