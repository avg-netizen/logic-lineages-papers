# Paper 17 — initial exact support low/high/empty split

[arithmetic.tex](../../../17-permitted-control-canonical-comparison/sections/arithmetic.tex), lines 242–265. Use one valuation-independent sufficient originalFamilyCeiling from the existing finite actual initial branch syntax and existing per-row bounds. For one supplied original shared normalized valuation, classify the true literal emitted support: a value below the ceiling, a nonempty support with every actual value at least the ceiling, or empty support. These strata are exhaustive and mutually exclusive (the first may have multiple low-coordinate witnesses). The same original positive graph, original prior, and requested terminal bit are used in every case.

[Targets](../../LogicLineages/PermittedControl/OriginalPrintedPlainMatrixInitialPartitionTargets.lean) · [Actual rank-zero funding and the three strata](../../LogicLineages/PermittedControl/OriginalPrintedPlainMatrixInitialPartitionFundingProof.lean) · [Full conditional packet split](../../LogicLineages/PermittedControl/OriginalPrintedPlainMatrixInitialPartitionProof.lean) · [Exact checks](../../LogicLineages/PermittedControl/OriginalPrintedPlainMatrixInitialPartitionStatementChecks.lean).
- Low: take one genuine support coordinate below the ceiling and the exact residual at the actual digit, including if the coordinate is a hidden wire. No other coordinate is reduced.
- Nonempty large: choose an actual enumerated equality/order guard. Any passing dense branch really has an original occurrence at rank zero; its original value pays the common ceiling. The high packet is on that same branch and valuation, with exact indexed signed traces.
- Empty: leave the original exact zero-coordinate case unchanged, with no ambient fake rank-zero payment. The arbitrary inherited prior is unchanged here as everywhere.

No later symbolic high branch generation, projection, dimension recursion, or plain/bounded arithmetic decision.
