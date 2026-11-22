# Paper 17 low-coordinate strips for one signed row

The original low-coordinate branch fixes each raw value below the finite cutoff and leaves the other coordinates unbounded. This packet enumerates those slices for one unprepared signed row with original coordinate, ordinary-value, and count terms. [Arithmetic, lines 249–254](../../../17-permitted-control-canonical-comparison/sections/arithmetic.tex#L249)

The effective code retains the entire ordered `List.range bound` with its literal original slice results, including invalid reads and genuine misses. On canonical weighted operand codes, every status and residual payload matches the original slice. [Frozen comparator](../../LogicLineages/PermittedControl/SignedRowLowStripsTargets.lean) · [Code proof](../../LogicLineages/PermittedControl/SignedRowLowStripsCodeProof.lean) · [Original pointwise slice](PAPER17-SIGNED-ROW-COORDINATE-SLICE-SOURCE-MAP.md)

An actual original row has an ordered successful read for each used occurrence. This excludes both failures of the slice at the selected raw value. A successful slice carries the original divisibility to its exact residual operands by the checked pointwise theorem. Both directions evaluate the inherited guard at the identical valuation obtained by updating one original rank. The guard is a supplied predicate on the raw valuation. [Semantic proof](../../LogicLineages/PermittedControl/SignedRowLowStripsSemanticProof.lean) · [Exact aliases](../../LogicLineages/PermittedControl/SignedRowLowStripsStatementChecks.lean)

The first source edition left the scope of the positive-modulus guard implicit in the syntax and the first code proof did not expose both range lists before induction. The current comparator parenthesizes the full equivalence. The earlier exact target, preflight, and rejected code edition are preserved. [Source pins](PAPER17-SIGNED-ROW-LOW-STRIPS-FROZEN.json) · [Earlier exact edition](p17-signed-row-low-strips-failed-proof-1795318515081525610-9/1795318515081525610-9.json)

The corresponding calculations for an entire matrix and the dimension-reducing recursion remain open. The cutoff is a supplied natural number here.
