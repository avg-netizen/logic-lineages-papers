# Exact topological sequential circuit for the printed original gate kinds

Paper 17, `17-permitted-control-canonical-comparison/sections/arithmetic.tex`, lines 3–11 and 33–54.

This explicit supplied schedule uses the checked exact original mixed affine/arbitrary fixed-head gates (#989) and all three newly checked original field reads (#1009): fixed (f) iterate, entry norm and interval count. A hit writes only the original new output. A field invalid input and a genuine first-entry miss are distinct failure reasons; either stops immediately. An original base rejection is separate, and none of these cases is assigned a default or Boolean false.

The topology protects every actual original named input occurrence, including repeated affine dependencies and shared earlier outputs. At fixed original external valuation the exact run succeeds iff the actual original graph conjunction holds at one unique final valuation agreeing at all non-produced names. Error iff no such extension exists. The caller supplies the schedule; there is no parser or automatic topological sorting. No grammar-wide normalization, new code effectivity, branch/cutoff, or complete closed-block arithmetic decision is claimed.
