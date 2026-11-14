# Guarded original head-result slots (exact3)

ExchangeLayer.input slots17/18 are generic Encodable type encodings of decoded source/target head results. TransparentMetadataFields.head extracts raw headNumber only on successful original validValue; malformed parameter/node branches return zero. OriginalHeadResult computes the actual six-case result-type constructor. Its value at raw zero is ground0, matching both invalid fieldValue branches (zero) and valid non-head constructors' default head .zero. NativeResults therefore asserts all vectors, not merely valid encoded terms.

InternalOrdinary and InternalNumbered use original raw constructors, actual V=1 graph, actual raw query graph, and actual head pair tag/payload graph. They conclude an iff with the concrete branchResult graph, not an assumed semantic decoding or a native reflection. The numbered output annotation tau is NOT confused with the head result; branchResult depends on rawHead's payload.

No installed tuple change yet. The current full package stays unchanged. HeadMove, guard semantic correctness and recursive dependency coverage/coherence remain open; this packet does not prove full E or class/source stability.
