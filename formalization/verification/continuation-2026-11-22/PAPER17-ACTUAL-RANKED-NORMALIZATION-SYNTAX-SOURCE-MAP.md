# Paper 17: source-stable grouping and exact rank-local replay

Manuscript: [arithmetic proof](../../../17-permitted-control-canonical-comparison/sections/arithmetic.tex), lines 197–220 (group true zero coefficients, compare exact largest class), 235–260 (least/all-larger rank split and greatest replay).

- SkeletonProof proves every actual successful checked read normalization has the same valuation-independent signed term skeleton. The syntax Finsupp depends only on literal weighted operand keys, coefficients and their source order, with no fake read value. It uses the same actual support order and aggregated weights as the checked reader; each retained nonzero operand was literally present. No claim that an invalid/missing source read can be dropped or normalized.
- RankProof proves the explicit strict extension of actual finite ranked support: preserve all lower values, use the supplied new greatest value, and continue strictly above it only outside the active support. No unsupported assumption that a raw update preserves old/global strictness for unbounded greatest updates.
- Exact rank locality keeps both original raw reader failure statuses, exact field domains/values, true ordered signed read vectors, actual original full-value labels, and tied lower prepared table under agreement at ranks through the greatest. It does not require or claim agreement on unused ranks above it.
- StatementChecks audits exact normalized skeleton, strict extension, reader locality and aggregate.

This is the genuine support and syntax supplier for a uniform branch assembler, not the assembler, symbolic zero transfer or arithmetic decision itself.
